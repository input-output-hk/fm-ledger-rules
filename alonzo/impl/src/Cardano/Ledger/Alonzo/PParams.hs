{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}

-- | This module contains just the type of protocol parameters.
module Cardano.Ledger.Alonzo.PParams
  ( PParams' (..),
    PParams,
    emptyPParams,
    ProtVer (..),
    ProposedPPUpdates (..),
    emptyPPPUpdates,
    PParamsUpdate,
    emptyPParamsUpdate,
    updatePParams,
    getLanguageView,
    LangDepView (..),
    PParamFeeInfo,
  )
where

import Cardano.Binary
  ( Annotator,
    FromCBOR (..),
    ToCBOR (..),
    encodePreEncoded,
  )
import Cardano.Ledger.Alonzo.Language (Language (..))
import Cardano.Ledger.Alonzo.Scripts
  ( CostModel,
    ExUnits (..),
    Prices (..),
  )
import qualified Cardano.Ledger.Core as Core
import Cardano.Ledger.Era
import Cardano.Ledger.SafeHash
  ( EraIndependentPParamView,
    HashAnnotated (..),
    SafeToHash (..),
  )
import Control.Applicative (liftA2)
import Control.DeepSeq (NFData)
import Data.ByteString.Short (fromShort)
import Data.Coders
  ( Decode (..),
    Density (..),
    Encode (..),
    Field (..),
    Wrapped (..),
    decode,
    encode,
    field,
    mapDecodeA,
    mapEncode,
    (!>),
    (<*!),
  )
import Data.Functor.Identity (Identity (..))
import Data.Kind (Type)
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Data.Maybe (fromMaybe)
import Data.MemoBytes (MemoBytes (..), memoBytes)
import Data.Typeable
import GHC.Generics (Generic)
import GHC.Records (HasField (..))
import NoThunks.Class (InspectHeapNamed (..), NoThunks (..))
import Numeric.Natural (Natural)
import Shelley.Spec.Ledger.BaseTypes
  ( Nonce (NeutralNonce),
    StrictMaybe (..),
    UnitInterval,
    interval0,
    strictMaybeToMaybe,
  )
import Shelley.Spec.Ledger.Coin (Coin (..))
import Shelley.Spec.Ledger.Keys (KeyHash, KeyRole (..))
import Shelley.Spec.Ledger.Orphans ()
import Shelley.Spec.Ledger.PParams (HKD, ProtVer (..))
import Shelley.Spec.Ledger.Serialization
  ( FromCBORGroup (..),
    ToCBORGroup (..),
    mapToCBOR,
    ratioFromCBOR,
    ratioToCBOR,
  )
import Shelley.Spec.Ledger.Slot (EpochNo (..))

-- ================================================================
-- TODO make type families for PParams and PParamsUpdate

-- How to handle this alonzo-specific type?
type PParamsUpdate era = PParams' StrictMaybe era

-- | Protocol parameters.
-- Shelley parameters + additional ones
data PParams' f era = PParams
  { -- | The linear factor for the minimum fee calculation
    _minfeeA :: !(HKD f Natural),
    -- | The constant factor for the minimum fee calculation
    _minfeeB :: !(HKD f Natural),
    -- | Maximal block body size
    _maxBBSize :: !(HKD f Natural),
    -- | Maximal transaction size
    _maxTxSize :: !(HKD f Natural),
    -- | Maximal block header size
    _maxBHSize :: !(HKD f Natural),
    -- | The amount of a key registration deposit
    _keyDeposit :: !(HKD f Coin),
    -- | The amount of a pool registration deposit
    _poolDeposit :: !(HKD f Coin),
    -- | epoch bound on pool retirement
    _eMax :: !(HKD f EpochNo),
    -- | Desired number of pools
    _nOpt :: !(HKD f Natural),
    -- | Pool influence
    _a0 :: !(HKD f Rational),
    -- | Monetary expansion
    _rho :: !(HKD f UnitInterval),
    -- | Treasury expansion
    _tau :: !(HKD f UnitInterval),
    -- | Decentralization parameter
    _d :: !(HKD f UnitInterval),
    -- | Extra entropy
    _extraEntropy :: !(HKD f Nonce),
    -- | Protocol version
    _protocolVersion :: !(HKD f ProtVer),
    -- | Minimum Stake Pool Cost
    _minPoolCost :: !(HKD f Coin),
    -- new/updated for alonzo

    -- | Cost in ada per byte of UTxO storage (instead of _minUTxOValue)
    _adaPerUTxOByte :: !(HKD f Coin),
    -- | Cost models for non-native script languages
    _costmdls :: !(HKD f (Map Language CostModel)),
    -- | Prices of execution units (for non-native script languages)
    _prices :: !(HKD f Prices),
    -- | Max total script execution resources units allowed per tx
    _maxTxExUnits :: !(HKD f ExUnits),
    -- | Max total script execution resources units allowed per block
    _maxBlockExUnits :: !(HKD f ExUnits)
  }
  deriving (Generic)

type PParams era = PParams' Identity era

deriving instance Eq (PParams' Identity era)

deriving instance Show (PParams' Identity era)

deriving instance NFData (PParams' Identity era)

instance NoThunks (PParams era)

instance (Era era) => ToCBOR (PParams era) where
  toCBOR
    PParams
      { _minfeeA = minfeeA',
        _minfeeB = minfeeB',
        _maxBBSize = maxBBSize',
        _maxTxSize = maxTxSize',
        _maxBHSize = maxBHSize',
        _keyDeposit = keyDeposit',
        _poolDeposit = poolDeposit',
        _eMax = eMax',
        _nOpt = nOpt',
        _a0 = a0',
        _rho = rho',
        _tau = tau',
        _d = d',
        _extraEntropy = extraEntropy',
        _protocolVersion = protocolVersion',
        _minPoolCost = minPoolCost',
        -- new/updated for alonzo
        _adaPerUTxOByte = adaPerUTxOByte',
        _costmdls = costmdls',
        _prices = prices',
        _maxTxExUnits = maxTxExUnits',
        _maxBlockExUnits = maxBlockExUnits'
      } =
      encode
        ( Rec (PParams @Identity)
            !> To minfeeA'
            !> To minfeeB'
            !> To maxBBSize'
            !> To maxTxSize'
            !> To maxBHSize'
            !> To keyDeposit'
            !> To poolDeposit'
            !> To eMax'
            !> To nOpt'
            !> E ratioToCBOR a0'
            !> To rho'
            !> To tau'
            !> To d'
            !> To extraEntropy'
            !> E toCBORGroup protocolVersion'
            !> To minPoolCost'
            -- new/updated for alonzo
            !> To adaPerUTxOByte'
            !> mapEncode costmdls'
            !> To prices'
            !> To maxTxExUnits'
            !> To maxBlockExUnits'
        )

instance
  (Era era) =>
  FromCBOR (Annotator (PParams era))
  where
  fromCBOR =
    decode $
      Ann (RecD PParams)
        <*! Ann From -- _minfeeA         :: Integer
        <*! Ann From -- _minfeeB         :: Natural
        <*! Ann From -- _maxBBSize       :: Natural
        <*! Ann From -- _maxTxSize       :: Natural
        <*! Ann From -- _maxBHSize       :: Natural
        <*! Ann From -- _keyDeposit      :: Coin
        <*! Ann From -- _poolDeposit     :: Coin
        <*! Ann From -- _eMax            :: EpochNo
        <*! Ann From -- _nOpt            :: Natural
        <*! Ann (D ratioFromCBOR) -- _a0              :: Rational
        <*! Ann From -- _rho             :: UnitInterval
        <*! Ann From -- _tau             :: UnitInterval
        <*! Ann From -- _d               :: UnitInterval
        <*! Ann From -- _extraEntropy    :: Nonce
        <*! Ann (D fromCBORGroup) -- _protocolVersion :: ProtVer
        <*! Ann From -- _minPoolCost     :: Natural
        -- new/updated for alonzo
        <*! Ann From -- _adaPerUTxOByte  :: Coin
        <*! mapDecodeA (Ann From) From -- _costmdls :: (Map Language CostModel)
        <*! Ann From -- _prices = prices',
        <*! Ann From -- _maxTxExUnits = maxTxExUnits',
        <*! Ann From -- _maxBlockExUnits = maxBlockExUnits'

-- | Returns a basic "empty" `PParams` structure with all zero values.
emptyPParams :: PParams era
emptyPParams =
  PParams
    { _minfeeA = 0,
      _minfeeB = 0,
      _maxBBSize = 0,
      _maxTxSize = 2048,
      _maxBHSize = 0,
      _keyDeposit = Coin 0,
      _poolDeposit = Coin 0,
      _eMax = EpochNo 0,
      _nOpt = 100,
      _a0 = 0,
      _rho = interval0,
      _tau = interval0,
      _d = interval0,
      _extraEntropy = NeutralNonce,
      _protocolVersion = ProtVer 0 0,
      _minPoolCost = mempty,
      -- new/updated for alonzo
      _adaPerUTxOByte = Coin 0,
      _costmdls = mempty,
      _prices = Prices (Coin 0) (Coin 0),
      _maxTxExUnits = ExUnits 0 0,
      _maxBlockExUnits = ExUnits 0 0
    }

deriving instance Eq (PParams' StrictMaybe era)

deriving instance Show (PParams' StrictMaybe era)

deriving instance Ord (PParams' StrictMaybe era)

deriving instance NFData (PParams' StrictMaybe era)

instance NoThunks (PParamsUpdate era)

-- =======================================================
-- A PParamsUpdate has StrictMaybe fields, we want to Sparse encode it, by
-- writing only those fields where the field is (SJust x), that is the role of
-- the local function (omitStrictMaybe key x)

fromSJust :: StrictMaybe a -> a
fromSJust (SJust x) = x
fromSJust SNothing = error "SNothing in fromSJust"

isSNothing :: StrictMaybe a -> Bool
isSNothing SNothing = True
isSNothing (SJust _) = False

encodePParamsUpdate ::
  PParamsUpdate era ->
  Encode ('Closed 'Sparse) (PParamsUpdate era)
encodePParamsUpdate ppup =
  Keyed PParams
    !> omitStrictMaybe 0 (_minfeeA ppup)
    !> omitStrictMaybe 1 (_minfeeB ppup)
    !> omitStrictMaybe 2 (_maxBBSize ppup)
    !> omitStrictMaybe 3 (_maxTxSize ppup)
    !> omitStrictMaybe 4 (_maxBHSize ppup)
    !> omitStrictMaybe 5 (_keyDeposit ppup)
    !> omitStrictMaybe 6 (_poolDeposit ppup)
    !> omitStrictMaybe 7 (_eMax ppup)
    !> omitStrictMaybe 8 (_nOpt ppup)
    !> Omit isSNothing (Key 9 (E (ratioToCBOR . fromSJust) (_a0 ppup)))
    !> omitStrictMaybe 10 (_rho ppup)
    !> omitStrictMaybe 11 (_tau ppup)
    !> omitStrictMaybe 12 (_d ppup)
    !> omitStrictMaybe 13 (_extraEntropy ppup)
    !> omitStrictMaybe 14 (_protocolVersion ppup)
    !> omitStrictMaybe 15 (_minPoolCost ppup)
    !> omitStrictMaybe 16 (_adaPerUTxOByte ppup)
    !> omitStrictMaybe 17 (_costmdls ppup)
    !> omitStrictMaybe 18 (_prices ppup)
    !> omitStrictMaybe 19 (_maxTxExUnits ppup)
    !> omitStrictMaybe 20 (_maxBlockExUnits ppup)
  where
    omitStrictMaybe key x = Omit isSNothing (Key key (E (toCBOR . fromSJust) x))

instance (Era era) => ToCBOR (PParamsUpdate era) where
  toCBOR ppup = encode (encodePParamsUpdate ppup)

emptyPParamsUpdate :: PParamsUpdate era
emptyPParamsUpdate =
  PParams
    { _minfeeA = SNothing,
      _minfeeB = SNothing,
      _maxBBSize = SNothing,
      _maxTxSize = SNothing,
      _maxBHSize = SNothing,
      _keyDeposit = SNothing,
      _poolDeposit = SNothing,
      _eMax = SNothing,
      _nOpt = SNothing,
      _a0 = SNothing,
      _rho = SNothing,
      _tau = SNothing,
      _d = SNothing,
      _extraEntropy = SNothing,
      _protocolVersion = SNothing,
      _minPoolCost = SNothing,
      -- new/updated for alonzo
      _adaPerUTxOByte = SNothing,
      _costmdls = SNothing,
      _prices = SNothing,
      _maxTxExUnits = SNothing,
      _maxBlockExUnits = SNothing
    }

-- ===============================================================================
-- To deserialise the Sparse encoding (produced by encodePParamsUpdate) where
-- 1) only the 'x' part of the (SJust x) has been serialized, and
-- 2) some fields only have FormCBOR(Annotated instances),
-- we need special functions for constructing Field decoders that handle both cases.

-- | if we have a normal (FromCBOR field) instance we use fieldNorm
fieldNorm :: (StrictMaybe field -> b -> b) -> Decode w field -> Field (Annotator b)
fieldNorm update dec = Field (liftA2 update) (decode (Ann (Map SJust dec)))

-- | if we only have a (FromCBOR (Annotator field)) instance we use fieldAnn
fieldAnn ::
  (StrictMaybe field -> b -> b) ->
  Decode w (Annotator field) ->
  Field (Annotator b)
fieldAnn update dec = Field (liftA2 update) (do x <- decode dec; pure (SJust <$> x))

updateField :: Word -> Field (Annotator (PParamsUpdate era))
updateField 0 = fieldNorm (\x up -> up {_minfeeA = x}) From
updateField 1 = fieldNorm (\x up -> up {_minfeeB = x}) From
updateField 2 = fieldNorm (\x up -> up {_maxBBSize = x}) From
updateField 3 = fieldNorm (\x up -> up {_maxTxSize = x}) From
updateField 4 = fieldNorm (\x up -> up {_maxBHSize = x}) From
updateField 5 = fieldNorm (\x up -> up {_keyDeposit = x}) From
updateField 6 = fieldNorm (\x up -> up {_poolDeposit = x}) From
updateField 7 = fieldNorm (\x up -> up {_eMax = x}) From
updateField 8 = fieldNorm (\x up -> up {_nOpt = x}) From
updateField 9 = fieldNorm (\x up -> up {_a0 = x}) (D ratioFromCBOR)
updateField 10 = fieldNorm (\x up -> up {_rho = x}) From
updateField 11 = fieldNorm (\x up -> up {_tau = x}) From
updateField 12 = fieldNorm (\x up -> up {_d = x}) From
updateField 13 = fieldNorm (\x up -> up {_extraEntropy = x}) From
updateField 14 = fieldNorm (\x up -> up {_protocolVersion = x}) From
updateField 15 = fieldNorm (\x up -> up {_minPoolCost = x}) From
updateField 16 = fieldNorm (\x up -> up {_adaPerUTxOByte = x}) From
updateField 17 = fieldAnn (\x up -> up {_costmdls = x}) (mapDecodeA (Ann From) From)
updateField 18 = fieldNorm (\x up -> up {_prices = x}) From
updateField 19 = fieldNorm (\x up -> up {_maxTxExUnits = x}) From
updateField 20 = fieldNorm (\x up -> up {_maxBlockExUnits = x}) From
updateField k = field (\_x up -> up) (Invalid k)

instance (Era era) => FromCBOR (Annotator (PParamsUpdate era)) where
  fromCBOR =
    decode
      (SparseKeyed "PParamsUpdate" (pure emptyPParamsUpdate) updateField [])

-- =================================================================

-- | Update operation for protocol parameters structure @PParams
newtype ProposedPPUpdates era
  = ProposedPPUpdates (Map (KeyHash 'Genesis (Crypto era)) (PParamsUpdate era))
  deriving (Show, Eq, Generic)

instance NFData (ProposedPPUpdates era)

instance NoThunks (ProposedPPUpdates era)

instance Era era => ToCBOR (ProposedPPUpdates era) where
  toCBOR (ProposedPPUpdates m) = mapToCBOR m

instance Era era => FromCBOR (Annotator (ProposedPPUpdates era)) where
  fromCBOR = (ProposedPPUpdates <$>) <$> (decode (mapDecodeA (Ann From) From)) -- splitMapFromCBOR fromCBOR fromCBOR

emptyPPPUpdates :: ProposedPPUpdates era
emptyPPPUpdates = ProposedPPUpdates Map.empty

updatePParams :: PParams era -> PParamsUpdate era -> PParams era
updatePParams pp ppup =
  PParams
    { _minfeeA = fromMaybe' (_minfeeA pp) (_minfeeA ppup),
      _minfeeB = fromMaybe' (_minfeeB pp) (_minfeeB ppup),
      _maxBBSize = fromMaybe' (_maxBBSize pp) (_maxBBSize ppup),
      _maxTxSize = fromMaybe' (_maxTxSize pp) (_maxTxSize ppup),
      _maxBHSize = fromMaybe' (_maxBHSize pp) (_maxBHSize ppup),
      _keyDeposit = fromMaybe' (_keyDeposit pp) (_keyDeposit ppup),
      _poolDeposit = fromMaybe' (_poolDeposit pp) (_poolDeposit ppup),
      _eMax = fromMaybe' (_eMax pp) (_eMax ppup),
      _nOpt = fromMaybe' (_nOpt pp) (_nOpt ppup),
      _a0 = fromMaybe' (_a0 pp) (_a0 ppup),
      _rho = fromMaybe' (_rho pp) (_rho ppup),
      _tau = fromMaybe' (_tau pp) (_tau ppup),
      _d = fromMaybe' (_d pp) (_d ppup),
      _extraEntropy = fromMaybe' (_extraEntropy pp) (_extraEntropy ppup),
      _protocolVersion = fromMaybe' (_protocolVersion pp) (_protocolVersion ppup),
      _minPoolCost = fromMaybe' (_minPoolCost pp) (_minPoolCost ppup),
      -- new/updated for alonzo
      _adaPerUTxOByte = fromMaybe' (_adaPerUTxOByte pp) (_adaPerUTxOByte ppup),
      _costmdls = fromMaybe' (_costmdls pp) (_costmdls ppup),
      _prices = fromMaybe' (_prices pp) (_prices ppup),
      _maxTxExUnits = fromMaybe' (_maxTxExUnits pp) (_maxTxExUnits ppup),
      _maxBlockExUnits = fromMaybe' (_maxBlockExUnits pp) (_maxBlockExUnits ppup)
    }
  where
    fromMaybe' :: a -> StrictMaybe a -> a
    fromMaybe' x = fromMaybe x . strictMaybeToMaybe

-- ===================================================
-- Figure 1: "Definitions Used in Protocol Parameters"

-- The Language Depenedent View type (LangDepView) is a GADT, it will have a
-- different Constructor for each Language. This way each language can have a
-- different view of the Protocol parameters. This is an intermediate type and
-- we introduce it only because we are interested in combining it with other
-- things so we can hash the combination. Thus this type (and the other things
-- we combine it with) must remember their original bytes. We make it a data
-- type around a MemoBytes. Unfortunately we can't use a newtype, because the
-- constructor must existentially hide the Language index. Instances on GADT's
-- are a bit tricky so we are carefull in the comments below to explain them.
-- Because we intend to add new languages the GADT will someday end up with more
-- constructors. So we add some commented out code that suggests how to extend
-- the instances when that happens.

data RawView :: Type -> Language -> Type where
  RawPlutusView :: CostModel -> RawView era 'PlutusV1

-- RawOtherView :: Int -> RawView era 'OtherLANG

deriving instance Eq (RawView era lang)

deriving instance Ord (RawView era lang)

deriving instance Show (RawView era lang)

deriving instance Typeable (RawView era lang)

deriving via InspectHeapNamed "RawView" (RawView e l) instance NoThunks (RawView e l)

instance (Typeable era) => ToCBOR (LangDepView era) where
  toCBOR (LangDepViewConstr (Memo _ bytes)) = encodePreEncoded (fromShort bytes)

pattern PlutusView :: CostModel -> LangDepView era
pattern PlutusView cm <-
  LangDepViewConstr (Memo (RawPlutusView cm) _)
  where
    PlutusView cm = LangDepViewConstr (memoBytes (Sum RawPlutusView 0 !> To cm))

-- Note the tag 0 ^
{- How to extend to another language
pattern OtherView :: Int -> LangDepView era
pattern OtherView n <- LangDepViewConstr (Memo (RawOtherView cm) _)
  where OtherView n = LangDepViewConstr (memoBytes (Sum RawOtherView 1 !> To n))
                                                  -- Note the tag 1  ^
-}

{-# COMPLETE PlutusView {- OtherView -} #-}

instance (Typeable era) => FromCBOR (Annotator (LangDepView era)) where
  fromCBOR = decode $ Summands "LangDepView" decodeTag
    where
      decodeTag :: Word -> Decode 'Open (Annotator (LangDepView era))
      decodeTag 0 = Ann (SumD PlutusView) <*! From
      -- Since CostModel has only (FromCBOR (Annotator CostModel) insatnce
      -- decodeTag 1 = Ann (SumD OtherView) <*! (Ann From)
      -- Since Int has FromCBOR instance
      decodeTag n = Invalid n

data LangDepView era where
  LangDepViewConstr :: (MemoBytes (RawView era lang)) -> LangDepView era

-- We can't derive SafeToHash via newtype deriving because LandDepViewConstr is
-- a data not a newtype. But it does remember its original bytes so we can add
-- the instance manually.

instance SafeToHash (LangDepView era) where
  originalBytes (LangDepViewConstr (Memo _ bs)) = fromShort bs

instance
  (Crypto era ~ c) =>
  HashAnnotated (LangDepView era) EraIndependentPParamView c

deriving via
  InspectHeapNamed "LangDepView" (LangDepView e)
  instance
    NoThunks (LangDepView e)

instance Show (LangDepView era) where
  show (PlutusView x) = show x

-- show (OtherView n) = Show n

instance Eq (LangDepView era) where
  (PlutusView x) == (PlutusView y) = x == y

-- (OtherView n) == (OtherView m) = n==m
--  _ == _ = False

instance Ord (LangDepView era) where
  compare (PlutusView x) (PlutusView y) = compare x y

-- compare (OtherView n) (OtherView m) = compare n m
-- compare x y = compare (rank x) (rank y)
--   where rank :: LangDepView era -> Int
--         rank (PlutusView _) = 1
--         rank (OtherView _) = 2

getLanguageView ::
  forall era.
  PParams era ->
  Language ->
  LangDepView era
getLanguageView pp PlutusV1 =
  case Map.lookup PlutusV1 (_costmdls pp) of
    Just x -> (PlutusView x)
    Nothing -> error ("CostModel map does not have cost for language: " ++ show PlutusV1)

type PParamFeeInfo era =
  ( HasField "_minfeeA" (Core.PParams era) Natural,
    HasField "_minfeeB" (Core.PParams era) Natural,
    HasField "_prices" (Core.PParams era) Prices
  )
