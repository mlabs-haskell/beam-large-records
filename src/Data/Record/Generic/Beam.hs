{-# OPTIONS_GHC -Wall #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE UndecidableSuperClasses #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeOperators #-}
module Data.Record.Generic.Beam where

import Data.Bifunctor
import Data.Char
import Data.Kind
import Data.Record.Generic
import Data.Record.Generic.Show
import qualified Data.Record.Generic.Rep as R
import Data.Record.TH
import Database.Beam.Schema.Tables
import Unsafe.Coerce
import Control.Applicative
import Data.Coerce
import qualified GHC.Generics as GHC
import qualified Data.Text as T
import Lens.Micro ((%~))
import GHC.TypeLits

-- * Beamable

-- | The generic code for the 'Beamable' class in beam-core distinguishes three different
-- shapes of fields. Simple fields are applications of 'Columnar', mixins / foreign key references
-- are references to other tables that are themselves 'Beamable', and nullable mixins are references
-- to other tables with an additional 'Nullable' flag (which essentially causes 'Maybe') to be
-- applied to all columns within that table.
--
data BeamField :: (Type -> Type) -> Type -> Type where
  SimpleBeamField        :: Columnar' f a -> BeamField f (Exposed a)
  MixinBeamField         :: Beamable tbl => tbl f -> BeamField f (tbl Exposed)
  NullableMixinBeamField :: Beamable tbl => tbl (Nullable f) -> BeamField f (tbl (Nullable Exposed))

-- | Once we know which form of beam fields we have to deal with, we can combine matching beam fields.
-- The code for this function corresponds to three different instances for the
-- 'Database.Beam.Schema.Tables.GZipTables' class, and is almost directly taken from there.
--
combineBeamFields ::
  forall f g h m b.
  (Applicative m)
  => (forall a. Columnar' f a -> Columnar' g a -> m (Columnar' h a))
  -> BeamField f b -> BeamField g b -> m (BeamField h b)
combineBeamFields combine (SimpleBeamField f)        (SimpleBeamField g)        = SimpleBeamField <$> combine f g
combineBeamFields combine (MixinBeamField f)         (MixinBeamField g)         = MixinBeamField <$> zipBeamFieldsM combine f g
combineBeamFields combine (NullableMixinBeamField f) (NullableMixinBeamField g) =
  NullableMixinBeamField <$> zipBeamFieldsM (adapt combine) f g
  where
    adapt ::
         (forall a. Columnar' f a -> Columnar' g a -> m (Columnar' h a))
      -> (forall a. Columnar' (Nullable f) a -> Columnar' (Nullable g) a -> m (Columnar' (Nullable h) a))
    adapt c fa ga = toNullable <$> c (fromNullable fa) (fromNullable ga)

    toNullable :: forall w a. Columnar' w (Maybe a) -> Columnar' (Nullable w) a
    toNullable = coerce

    fromNullable :: forall w a. Columnar' (Nullable w) a -> Columnar' w (Maybe a)
    fromNullable = coerce

-- | In the constraint 'CheckBeamField f b', the type @b@ is supposed to be the type
-- of a field of some type @tbl f@ where @f@ has been instantiated to 'Exposed'.
--
-- 'Exposed' is defined within beam-core and can be used to distinguish the different
-- kinds of fields we are interested in.
--
-- From the shape of @b@, we can then learn the shape of @tbl f@ if @f@ is unknown.
--
-- Each of the instances are corresponding to one of the constructors of 'BeamField'.
--
class CheckBeamField f b where
  -- | If @tbl Exposed@ has a field of type @b@, then @tbl f@ is supposed to
  -- have the type @OriginalType f b@.
  type family OriginalType f b :: Type
  checkBeamField :: OriginalType f b -> BeamField f b
  uncheckBeamField :: BeamField f b -> OriginalType f b

-- If a field in the table is of shape @Columnar f x@, then @Columnar Exposed x@
-- reduces to @Exposed x@. So in turn we're assuming that if we observe @Exposed x@,
-- we require the shape of the field to be @Columnar f x@.
--
instance CheckBeamField f (Exposed x) where
  type OriginalType f (Exposed x) = Columnar f x
  checkBeamField x = SimpleBeamField (Columnar' x)
  uncheckBeamField (SimpleBeamField (Columnar' x)) = x

-- If a field in the table is of shape @tbl f@, then we observe @tbl Exposed@
-- on the instantiation to @Exposed@.
--
instance (Beamable tbl) => CheckBeamField f (tbl Exposed) where
  type OriginalType f (tbl Exposed) = tbl f
  checkBeamField x = MixinBeamField x
  uncheckBeamField (MixinBeamField x) = x

-- If a field in the table is of shape @tbl (Nullable f)@, then we observe
-- @tbl (Nullable Exposed)@ on the instantiation to @Exposed@.
--
instance (Beamable tbl) => CheckBeamField f (tbl (Nullable Exposed)) where
  type OriginalType f (tbl (Nullable Exposed)) = tbl (Nullable f)
  checkBeamField x = NullableMixinBeamField x
  uncheckBeamField (NullableMixinBeamField x) = x

-- | Require all fields in a table to be in one of the three beam field
-- cases, by traversing the constraints corresponding to @tbl Exposed@.
--
type CheckBeamFields f tbl = (Constraints (tbl Exposed) (CheckBeamField f))

-- | Corresponds roughly to the 'gTblSkeleton' implementation in the
-- 'GTableSkeleton' class.
--
-- Code is taken from the instances of that class.
--
class IgnoreBeamField (a :: Type) where
  ignoreBeamField :: BeamField Ignored a

instance IgnoreBeamField (Exposed x) where
  ignoreBeamField = SimpleBeamField (Columnar' Ignored)

instance Beamable tbl => IgnoreBeamField (tbl Exposed) where
  ignoreBeamField = MixinBeamField tblSkeleton

instance Beamable tbl => IgnoreBeamField (tbl (Nullable Exposed)) where
  ignoreBeamField = NullableMixinBeamField (unI (zipBeamFieldsM transform tblSkeleton tblSkeleton))
    where
      transform :: Columnar' Ignored a -> Columnar' Ignored a -> I (Columnar' (Nullable Ignored) a)
      transform _ _ = I (Columnar' Ignored)

newtype O f a = O { unO :: OriginalType f a }

-- | Coercion that makes use of the identity we have for 'OriginalType'.
-- For every field @b@ contained in @tbl Exposed@, we know that @OriginalType f b@
-- is the corresponding field of @tbl f@.
--
expose :: CheckBeamFields f tbl => Rep I (tbl f) -> Rep (O f) (tbl Exposed)
expose = unsafeCoerce
{-# NOINLINE expose #-}

-- | Inverse of 'expose', using the same type identity.
--
unexpose :: CheckBeamFields f tbl => Rep (O f) (tbl Exposed) -> Rep I (tbl f)
unexpose = unsafeCoerce
{-# NOINLINE unexpose #-}

checkBeamFields ::
  forall f tbl. (Generic (tbl Exposed), CheckBeamFields f tbl)
  => Rep I (tbl f) -> Rep (BeamField f) (tbl Exposed)
checkBeamFields = R.cmap (Proxy @(CheckBeamField f)) (checkBeamField . unO) . expose

uncheckBeamFields :: forall f tbl. (Generic (tbl Exposed), CheckBeamFields f tbl)
  => CheckBeamFields f tbl => Rep (BeamField f) (tbl Exposed) -> Rep I (tbl f)
uncheckBeamFields = unexpose . R.cmap (Proxy @(CheckBeamField f)) (O . uncheckBeamField)

-- | Generic implementation of 'zipBeamFieldsM' that can be used in 'Beamable' instances.
gzipBeamFieldsM ::
  forall tbl f g h m.
  ( Applicative m
  , Generic (tbl f)
  , Generic (tbl g)
  , Generic (tbl h)
  , Generic (tbl Exposed)
  , CheckBeamFields f tbl
  , CheckBeamFields g tbl
  , CheckBeamFields h tbl
  )
  => (forall a. Columnar' f a -> Columnar' g a -> m (Columnar' h a))
  -> tbl f -> tbl g -> m (tbl h)
gzipBeamFieldsM combine f g =
  to <$> zipBeamFieldsM_Rep combine (from f) (from g)

zipBeamFieldsM_Rep ::
  forall tbl f g h m.
  ( Applicative m
  , Generic (tbl f)
  , Generic (tbl g)
  , Generic (tbl h)
  , Generic (tbl Exposed)
  , CheckBeamFields f tbl
  , CheckBeamFields g tbl
  , CheckBeamFields h tbl
  )
  => (forall a. Columnar' f a -> Columnar' g a -> m (Columnar' h a))
  -> Rep I (tbl f) -> Rep I (tbl g) -> m (Rep I (tbl h))
zipBeamFieldsM_Rep combine f g =
  let
    ef :: Rep (BeamField f) (tbl Exposed)
    ef = checkBeamFields f

    eg :: Rep (BeamField g) (tbl Exposed)
    eg = checkBeamFields g

    eh :: m (Rep (BeamField h) (tbl Exposed))
    eh = R.zipWithM (combineBeamFields combine) ef eg

    h :: m (Rep I (tbl h))
    h = uncheckBeamFields <$> eh
  in
    h

-- | Generic implementation of 'tblSkeleton' that can be used in 'Beamable' instances.
gtblSkeleton ::
  forall tbl.
  ( Generic (tbl Ignored)
  , Generic (tbl Exposed)
  , Constraints (tbl Exposed) IgnoreBeamField
  , CheckBeamFields Ignored tbl
  )
  => TableSkeleton tbl
gtblSkeleton =
  let
    e :: Rep (BeamField Ignored) (tbl Exposed)
    e = R.cpure (Proxy @IgnoreBeamField) ignoreBeamField
  in
    to (uncheckBeamFields e)

-- * Database

data Reqs = DefaultReqs | RegularReqs | LRReqs

type family InterpretReqs (reqs :: Reqs) (be :: Type) (tbl :: Type) :: Constraint where
  -- InterpretReqs 'DefaultReqs be tbl = DatabaseEntityDefaultRequirements be tbl
  InterpretReqs 'LRReqs      be tbl = DatabaseEntityLRRequirements      be tbl
  InterpretReqs 'RegularReqs be tbl = DatabaseEntityRegularRequirements be tbl

data DatabaseField :: Reqs -> Type -> (Type -> Type) -> Type -> Type where
  DatabaseEntityField :: (IsDatabaseEntity be tbl, InterpretReqs reqs be tbl) => f tbl -> DatabaseField reqs be f (Exposed tbl)

combineDatabaseFields ::
  forall reqs be f g h m x.
  (Applicative m)
  => (forall tbl. (IsDatabaseEntity be tbl, InterpretReqs reqs be tbl) => f tbl -> g tbl -> m (h tbl))
  -> DatabaseField reqs be f x -> DatabaseField reqs be g x -> m (DatabaseField reqs be h x)
combineDatabaseFields combine (DatabaseEntityField f) (DatabaseEntityField g) = DatabaseEntityField <$> combine f g

class CheckDatabaseField (reqs :: Reqs) be (f :: Type -> Type) (tbl :: Type) where
  type OriginalDatabaseType f tbl :: Type
  checkDatabaseField :: OriginalDatabaseType f tbl -> DatabaseField reqs be f tbl
  uncheckDatabaseField :: DatabaseField reqs be f tbl -> OriginalDatabaseType f tbl

instance (IsDatabaseEntity be tbl, InterpretReqs reqs be tbl) => CheckDatabaseField reqs be f (Exposed tbl) where
  type OriginalDatabaseType f (Exposed tbl) = f tbl
  checkDatabaseField x = DatabaseEntityField x
  uncheckDatabaseField (DatabaseEntityField x) = x

type CheckDatabaseFields reqs be f (db :: (Type -> Type) -> Type) = (Constraints (db Exposed) (CheckDatabaseField reqs be f))

newtype D f tbl = D { unD :: OriginalDatabaseType f tbl }

dbExpose :: CheckDatabaseFields reqs be f db => Rep I (db f) -> Rep (D f) (db Exposed)
dbExpose = unsafeCoerce
{-# NOINLINE dbExpose #-}

dbUnexpose :: CheckDatabaseFields reqs be f db => Rep (D f) (db Exposed) -> Rep I (db f)
dbUnexpose = unsafeCoerce
{-# NOINLINE dbUnexpose #-}

checkDatabaseFields ::
  forall reqs be f db. (Generic (db Exposed), CheckDatabaseFields reqs be f db)
  => Rep I (db f) -> Rep (DatabaseField reqs be f) (db Exposed)
checkDatabaseFields = R.cmap (Proxy @(CheckDatabaseField reqs be f)) (checkDatabaseField . unD) . dbExpose @reqs @be

uncheckDatabaseFields ::
  forall reqs be f db. (Generic (db Exposed), CheckDatabaseFields reqs be f db)
  => Rep (DatabaseField reqs be f) (db Exposed) -> Rep I (db f)
uncheckDatabaseFields = dbUnexpose @reqs @be . R.cmap (Proxy @(CheckDatabaseField reqs be f)) (D . uncheckDatabaseField)

gzipTables ::
  forall be db f g h m.
  ( Applicative m
  , Generic (db f)
  , Generic (db g)
  , Generic (db h)
  , Generic (db Exposed)
  , CheckDatabaseFields 'RegularReqs be f db
  , CheckDatabaseFields 'RegularReqs be g db
  , CheckDatabaseFields 'RegularReqs be h db
  )
  => Proxy be
  -> (forall tbl. (IsDatabaseEntity be tbl, DatabaseEntityRegularRequirements be tbl) => f tbl -> g tbl -> m (h tbl))
  -> db f -> db g -> m (db h)
gzipTables _ combine f g =
  to <$> gzipTables_Rep @be combine (from f) (from g)

gzipTables_Rep ::
  forall be db f g h m.
  ( Applicative m
  , Generic (db f)
  , Generic (db g)
  , Generic (db h)
  , Generic (db Exposed)
  , CheckDatabaseFields 'RegularReqs be f db
  , CheckDatabaseFields 'RegularReqs be g db
  , CheckDatabaseFields 'RegularReqs be h db
  )
  => (forall tbl. (IsDatabaseEntity be tbl, DatabaseEntityRegularRequirements be tbl) => f tbl -> g tbl -> m (h tbl))
  -> Rep I (db f) -> Rep I (db g) -> m (Rep I (db h))
gzipTables_Rep combine f g =
  let
    ef :: Rep (DatabaseField 'RegularReqs be f) (db Exposed)
    ef = checkDatabaseFields f

    eg :: Rep (DatabaseField 'RegularReqs be g) (db Exposed)
    eg = checkDatabaseFields g

    eh :: m (Rep (DatabaseField 'RegularReqs be h) (db Exposed))
    eh = R.zipWithM (combineDatabaseFields combine) ef eg

    h :: m (Rep I (db h))
    h = uncheckDatabaseFields <$> eh
  in
    h

class AutoDbSetting be (tbl :: Type) where
  autoDbSetting :: String -> DatabaseField 'LRReqs be (DatabaseEntity be db) tbl

instance (IsDatabaseEntity' be tbl, DatabaseEntityLRRequirements be tbl) => AutoDbSetting be (Exposed tbl) where
  autoDbSetting fname = DatabaseEntityField (DatabaseEntity (dbEntityLRAuto @be (T.pack fname)))
  -- TODO: The use of `dbEntityAuto` here is wrong. It relies on `DatabaseEntityDefaultRequirements`,
  -- which in turn relies on `GDefaultTableFieldSettings`, which works on the GHC.Generics representation
  -- by using `defTblFieldSettings`. I think we have to replace these as well.

class IsDatabaseEntity be entityType => IsDatabaseEntity' be entityType where
  type DatabaseEntityLRRequirements be entityType :: Constraint
  dbEntityLRAuto :: DatabaseEntityLRRequirements be entityType => T.Text -> DatabaseEntityDescriptor be entityType

instance Beamable tbl => IsDatabaseEntity' be (TableEntity tbl) where
  type DatabaseEntityLRRequirements be (TableEntity tbl) =
    ( Table tbl
    , Generic (tbl (TableField tbl))
    , Constraints (tbl (TableField tbl)) CheckTblField
    )
  dbEntityLRAuto nm =
    DatabaseTable Nothing nm (unCamelCaseSel nm) autoTblSettings

instance Beamable tbl => IsDatabaseEntity' be (ViewEntity tbl) where
  type DatabaseEntityLRRequirements be (ViewEntity tbl) =
    ( Table tbl
    , Generic (tbl (TableField tbl))
    , Constraints (tbl (TableField tbl)) CheckTblField
    )
  dbEntityLRAuto nm =
    DatabaseView Nothing nm (unCamelCaseSel nm) autoTblSettings

instance IsDatabaseEntity' be (DomainTypeEntity ty) where
  type DatabaseEntityLRRequirements be (DomainTypeEntity ty) = ()
  dbEntityLRAuto =
    DatabaseDomainType Nothing

class CheckTblField a where
  tblField :: T.Text -> a

instance CheckTblField (TableField tbl a) where
  tblField fname =
    TableField (pure fname) (unCamelCaseSel fname)

instance
  ( ChooseSubTableStrategy tbl sub ~ strategy
  , SubTableStrategyImpl strategy f sub
  , TagReducesTo f (TableField tbl)
  , Beamable sub
  )
  => CheckTblField (sub f) where
  tblField origSelName =
    let
      tbl :: sub f
      tbl = namedSubTable (Proxy @strategy)

      relName :: T.Text
      relName = unCamelCaseSel origSelName

      settings' :: sub f
      settings' =
        changeBeamRep (reduceTag %~ \(Columnar' (TableField path nm)) -> Columnar' (TableField (pure origSelName <> path) (relName <> "__" <> nm))) tbl
    in
      settings'

class SubTableStrategyImpl (strategy :: SubTableStrategy) (f :: Type -> Type) sub where
  namedSubTable :: Proxy strategy -> sub f

instance
  ( Generic (sub f)
  , Constraints (sub (TableField tbl)) CheckTblField
  , f ~ TableField tbl
  )
  => SubTableStrategyImpl 'BeamableStrategy f sub where
  namedSubTable _ = autoTblSettings

instance
  ( Generic (rel (TableField rel))
  , Constraints (rel (TableField rel)) CheckTblField
  , TagReducesTo f (TableField tbl)
  , Table rel
  )
  => SubTableStrategyImpl 'PrimaryKeyStrategy f (PrimaryKey rel) where
  namedSubTable _ =
    primaryKey
      (changeBeamRep
        (\ (Columnar' (TableField path nm)) ->
          unI (reduceTag (\ _ -> pure (Columnar' (TableField path nm))) undefined)
        )
        (autoTblSettings @rel @rel)
      )

instance
  ( CheckNullable f
  , SubTableStrategyImpl 'PrimaryKeyStrategy f (PrimaryKey rel)
  )
  => SubTableStrategyImpl 'RecursiveKeyStrategy f (PrimaryKey rel) where
  namedSubTable _ =
    namedSubTable (Proxy @'PrimaryKeyStrategy)

autoTblSettings ::
  forall tbl tbl'.
  ( Generic (tbl (TableField tbl'))
  , Constraints (tbl (TableField tbl')) CheckTblField
  )
  => tbl (TableField tbl')
autoTblSettings =
  let
    fnames :: Rep (K String) (tbl (TableField tbl'))
    fnames = recordFieldNames (metadata (Proxy @(tbl (TableField tbl'))))

    tblFields :: Rep I (tbl (TableField tbl'))
    tblFields = R.cmap (Proxy @CheckTblField) (\ (K n) -> I (tblField (T.pack n))) fnames
  in
    to tblFields

autoDbSettings ::
  forall be db.
  ( Generic (db (DatabaseEntity be db))
  , Generic (db Exposed)
  , Constraints (db Exposed) (AutoDbSetting be)
  , CheckDatabaseFields 'LRReqs be (DatabaseEntity be db) db
  )
  => DatabaseSettings be db
autoDbSettings =
  let
    fnames :: Rep (K String) (db Exposed)
    fnames = recordFieldNames (metadata (Proxy @(db Exposed)))

    e :: Rep (DatabaseField 'LRReqs be (DatabaseEntity be db)) (db Exposed)
    e = R.cmap (Proxy @(AutoDbSetting be)) (autoDbSetting . unK) fnames
  in
    to (uncheckDatabaseFields e)

-- * Utilities (should be exported from Beam)

unCamelCaseSel :: T.Text -> T.Text
unCamelCaseSel original =
  let symbolLeft = T.dropWhile (=='_') original
  in if T.null symbolLeft
     then original
     else if T.any (=='_') symbolLeft
          then symbolLeft
          else case unCamelCase symbolLeft of
                 [] -> symbolLeft
                 [xs] -> xs
                 _:xs -> T.intercalate "_" xs

unCamelCase :: T.Text -> [T.Text]
unCamelCase "" = []
unCamelCase s
    | (comp, next) <- T.break isUpper s, not (T.null comp) =
          let next' = maybe mempty (uncurry T.cons . first toLower) (T.uncons next)
          in T.toLower comp:unCamelCase next'
    | otherwise =
          let (comp, next) = T.span isUpper s
              next' = maybe mempty (uncurry T.cons . first toLower) (T.uncons next)
          in T.toLower comp:unCamelCase next'

type family ChooseSubTableStrategy (tbl :: (Type -> Type) -> Type) (sub :: (Type -> Type) -> Type) :: SubTableStrategy where
  ChooseSubTableStrategy tbl (PrimaryKey tbl) = 'RecursiveKeyStrategy
  ChooseSubTableStrategy tbl (PrimaryKey rel) = 'PrimaryKeyStrategy
  ChooseSubTableStrategy tbl sub = 'BeamableStrategy

data SubTableStrategy
  = PrimaryKeyStrategy
  | BeamableStrategy
  | RecursiveKeyStrategy

type family CheckNullable (f :: Type -> Type) :: Constraint where
  CheckNullable (Nullable f) = ()
  CheckNullable f = TypeError ('Text "Recursive references without Nullable constraint form an infinite loop." ':$$:
                               'Text "Hint: Only embed nullable 'PrimaryKey tbl' within the definition of 'tbl'." ':$$:
                               'Text "      For example, replace 'PrimaryKey tbl f' with 'PrimaryKey tbl (Nullable f)'")

-- * Example

largeRecord defaultLazyOptions [d|
     data LRTableA (f :: Type -> Type) =
       MkLRTableA
         { fldA1 :: Columnar f Int
         , fldA2 :: Columnar f Int
         }
  |]

largeRecord defaultLazyOptions [d|
     data LRTableB (f :: Type -> Type) =
       MkLRTableB
         { fldB1 :: Columnar f Int
         , fldB2 :: Columnar f Int
         , fldB3 :: Columnar f Bool
         , fldB4 :: Columnar f Char
         , fldB5 :: Columnar f Int
         , fldB6 :: Columnar f String
         , fldB7 :: LRTableA f
         , fldB8 :: PrimaryKey LRTableA f
         , fldB9 :: PrimaryKey LRTableA (Nullable f)
         }
  |]

largeRecord defaultLazyOptions [d|
     data LRDB (f :: Type -> Type) =
       MkLRDB
         { tblA :: f (TableEntity LRTableA)
         , tblB :: f (TableEntity LRTableB)
         }
  |]

instance Show (LRTableA Maybe) where
  showsPrec = gshowsPrec

instance Show (LRTableA (Nullable Maybe)) where
  showsPrec = gshowsPrec

instance Show (LRTableA (TableField tbl)) where
  showsPrec = gshowsPrec

instance Show (LRTableA (Nullable (TableField tbl))) where
  showsPrec = gshowsPrec

instance Show (LRTableB Maybe) where
  showsPrec = gshowsPrec

instance Show (LRTableB (TableField tbl)) where
  showsPrec = gshowsPrec

-- instance Show (LRDB (DatabaseEntity be LRDB)) where
--   showsPrec = gshowsPrec

-- deriving instance Show (TableSettings tbl) => Show (DatabaseEntityDescriptor be (TableEntity tbl))
-- deriving instance Show (TableSettings tbl) => Show (DatabaseEntity be db (TableEntity tbl))

instance Beamable LRTableA where
  zipBeamFieldsM = gzipBeamFieldsM
  tblSkeleton = gtblSkeleton

instance Beamable LRTableB where
  zipBeamFieldsM = gzipBeamFieldsM
  tblSkeleton = gtblSkeleton

instance Table LRTableA where
  newtype PrimaryKey LRTableA f = LRTableAKey (Columnar f Int)
    deriving (GHC.Generic)
  primaryKey = LRTableAKey . fldA1

instance Beamable (PrimaryKey LRTableA) -- using standard derivation via GHC.Generics
deriving instance Show (PrimaryKey LRTableA Maybe)
deriving instance Show (PrimaryKey LRTableA (Nullable Maybe))
deriving instance Show (PrimaryKey LRTableA (TableField tbl))
deriving instance Show (PrimaryKey LRTableA (Nullable (TableField tbl)))

instance Table LRTableB where
  data PrimaryKey LRTableB f = LRTableBKey (Columnar f Int)
    deriving (GHC.Generic)
  primaryKey = LRTableBKey . fldB1

instance Beamable (PrimaryKey LRTableB) -- using standard derivation via GHC.Generics
deriving instance Show (PrimaryKey LRTableB Maybe)
deriving instance Show (PrimaryKey LRTableB (TableField tbl))

instance Database be LRDB where
  zipTables = gzipTables

ex1 :: LRTableB Maybe
ex1 =
  [lr| MkLRTableB |]
    (Just 2)
    (Just 2)
    Nothing
    (Just 'x')
    (Just 4)
    Nothing
    ([lr| MkLRTableA |] (Just 8) Nothing)
    (LRTableAKey (Just 11))
    (LRTableAKey Nothing)

ex2 :: LRTableB Maybe
ex2 =
  [lr| MkLRTableB |]
    Nothing
    (Just 3)
    Nothing
    Nothing
    Nothing
    (Just "foo")
    ([lr| MkLRTableA |] Nothing (Just 9))
    (LRTableAKey (Just 22))
    (LRTableAKey (Just Nothing))

ex3 :: I (LRTableB Maybe)
ex3 = zipBeamFieldsM (\ (Columnar' x) (Columnar' y) -> I (Columnar' (x <|> y))) ex1 ex2

exDbSettings :: DatabaseSettings be LRDB
exDbSettings = autoDbSettings
