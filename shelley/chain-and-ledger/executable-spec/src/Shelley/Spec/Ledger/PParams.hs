{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}

-- | This module contains just the type of protocol parameters.
module Shelley.Spec.Ledger.PParams
  ( PParams' (..),
    PParams,
    emptyPParams,
    HKD,
    ProtVer (..),
    PPUpdateEnv (..),
    ProposedPPUpdates (..),
    emptyPPPUpdates,
    PParamsUpdate,
    emptyPParamsUpdate,
    Update (..),
    updatePParams,
  )
where

import Cardano.Binary
  ( FromCBOR (..),
    ToCBOR (..),
    decodeWord,
    encodeListLen,
    encodeMapLen,
    encodeWord,
  )
import Cardano.Ledger.Era
import Cardano.Ledger.Shelley.Constraints (UsesPParams (PParamsDelta))
import Control.DeepSeq (NFData)
import Control.Monad (unless)
import Data.Aeson (FromJSON (..), ToJSON (..), (.!=), (.:), (.:?), (.=))
import qualified Data.Aeson as Aeson
import Data.Coders
  ( Annotator (..),
    Decode (Ann, Emit, From, RecD),
    decode,
    mapDecodeA,
    (<*!),
  )
import Data.Default.Class (Default, def)
import Data.Foldable (fold)
import Data.Functor.Identity (Identity)
import Data.List (nub)
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Data.Maybe (fromMaybe, mapMaybe)
import Data.Scientific (Scientific)
import GHC.Generics (Generic)
import NoThunks.Class (NoThunks (..))
import Numeric.Natural (Natural)
import Shelley.Spec.Ledger.BaseTypes
  ( Nonce (NeutralNonce),
    StrictMaybe (..),
    UnitInterval,
    interval0,
    invalidKey,
    strictMaybeToMaybe,
  )
import Shelley.Spec.Ledger.Coin (Coin (..))
import Shelley.Spec.Ledger.Keys (GenDelegs, KeyHash, KeyRole (..))
import Shelley.Spec.Ledger.Orphans ()
import Shelley.Spec.Ledger.Serialization
  ( CBORGroup (..),
    FromCBORGroup (..),
    ToCBORGroup (..),
    decodeMapContents,
    decodeRecordNamed,
    mapFromCBOR,
    mapToCBOR,
    ratioFromCBOR,
    ratioToCBOR,
  )
import Shelley.Spec.Ledger.Slot (EpochNo (..), SlotNo (..))

-- | Higher Kinded Data
type family HKD f a where
  HKD Identity a = a
  HKD f a = f a

-- | Protocol parameters.
--
-- We use the HKD type family so that the protocol parameters type and
-- the type for the updates to the protocol parameters can share records fields.
-- The protocol parameters will have type 'PParams'' 'Identity', and the updates
-- will have type 'PParams'' 'StrictMaybe', though 'Identity' will be hidden from use.
--
-- For example:
--
-- @
--   myParameters =
--     PParams
--       { _minfeeA = 0,
--         _minfeeB = 0,
--         ...
--       }
--
--   myUpdate =
--     PParamsUpdate
--       { _minfeeA = SNothing,
--         _minfeeB = SJust 42,
--         ...
--       }
-- @
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
    -- | Minimum UTxO value
    _minUTxOValue :: !(HKD f Coin),
    -- | Minimum Stake Pool Cost
    _minPoolCost :: !(HKD f Coin)
  }
  deriving (Generic)

type PParams era = PParams' Identity era

deriving instance Eq (PParams' Identity era)

deriving instance Show (PParams' Identity era)

deriving instance NFData (PParams' Identity era)

data ProtVer = ProtVer {pvMajor :: !Natural, pvMinor :: !Natural}
  deriving (Show, Eq, Generic, Ord, NFData)
  deriving (ToCBOR) via (CBORGroup ProtVer)
  deriving (FromCBOR) via (CBORGroup ProtVer)

instance NoThunks ProtVer

instance ToJSON ProtVer where
  toJSON (ProtVer major minor) =
    Aeson.object
      [ "major" .= major,
        "minor" .= minor
      ]

instance FromJSON ProtVer where
  parseJSON =
    Aeson.withObject "ProtVer" $ \obj ->
      ProtVer
        <$> obj .: "major"
        <*> obj .: "minor"

instance ToCBORGroup ProtVer where
  toCBORGroup (ProtVer x y) = toCBOR x <> toCBOR y
  encodedGroupSizeExpr size proxy =
    encodedSizeExpr size ((\(ProtVer x _) -> toWord x) <$> proxy)
      + encodedSizeExpr size ((\(ProtVer _ y) -> toWord y) <$> proxy)
    where
      toWord :: Natural -> Word
      toWord = fromIntegral

  listLen _ = 2
  listLenBound _ = 2

instance FromCBORGroup ProtVer where
  fromCBORGroup = do
    x <- fromCBOR
    y <- fromCBOR
    pure $ ProtVer x y

instance NoThunks (PParams era)

instance (Era era) => ToCBOR (PParams era) where
  toCBOR
    ( PParams
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
          _minUTxOValue = minUTxOValue',
          _minPoolCost = minPoolCost'
        }
      ) =
      encodeListLen 18
        <> toCBOR minfeeA'
        <> toCBOR minfeeB'
        <> toCBOR maxBBSize'
        <> toCBOR maxTxSize'
        <> toCBOR maxBHSize'
        <> toCBOR keyDeposit'
        <> toCBOR poolDeposit'
        <> toCBOR eMax'
        <> toCBOR nOpt'
        <> ratioToCBOR a0'
        <> toCBOR rho'
        <> toCBOR tau'
        <> toCBOR d'
        <> toCBOR extraEntropy'
        <> toCBORGroup protocolVersion'
        <> toCBOR minUTxOValue'
        <> toCBOR minPoolCost'

instance (Era era) => FromCBOR (PParams era) where
  fromCBOR = do
    decodeRecordNamed "PParams" (const 18) $
      PParams
        <$> fromCBOR -- _minfeeA         :: Integer
        <*> fromCBOR -- _minfeeB         :: Natural
        <*> fromCBOR -- _maxBBSize       :: Natural
        <*> fromCBOR -- _maxTxSize       :: Natural
        <*> fromCBOR -- _maxBHSize       :: Natural
        <*> fromCBOR -- _keyDeposit      :: Coin
        <*> fromCBOR -- _poolDeposit     :: Coin
        <*> fromCBOR -- _eMax            :: EpochNo
        <*> fromCBOR -- _nOpt            :: Natural
        <*> ratioFromCBOR -- _a0         :: Rational
        <*> fromCBOR -- _rho             :: UnitInterval
        <*> fromCBOR -- _tau             :: UnitInterval
        <*> fromCBOR -- _d               :: UnitInterval
        <*> fromCBOR -- _extraEntropy    :: Nonce
        <*> fromCBORGroup -- _protocolVersion :: ProtVer
        <*> fromCBOR -- _minUTxOValue    :: Natural
        <*> fromCBOR -- _minPoolCost     :: Natural

-- | Annotated decoder instance for PParams. This is not needed in the Shelley
-- era, since PParams can be decoded without their annotation. But future eras
-- will require the annotation.
instance Era era => FromCBOR (Annotator (PParams era)) where
  fromCBOR = pure <$> fromCBOR

instance ToJSON (PParams era) where
  toJSON pp =
    Aeson.object
      [ "minFeeA" .= _minfeeA pp,
        "minFeeB" .= _minfeeB pp,
        "maxBlockBodySize" .= _maxBBSize pp,
        "maxTxSize" .= _maxTxSize pp,
        "maxBlockHeaderSize" .= _maxBHSize pp,
        "keyDeposit" .= _keyDeposit pp,
        "poolDeposit" .= _poolDeposit pp,
        "eMax" .= _eMax pp,
        "nOpt" .= _nOpt pp,
        "a0" .= (fromRational (_a0 pp) :: Scientific),
        "rho" .= _rho pp,
        "tau" .= _tau pp,
        "decentralisationParam" .= _d pp,
        "extraEntropy" .= _extraEntropy pp,
        "protocolVersion" .= _protocolVersion pp,
        "minUTxOValue" .= _minUTxOValue pp,
        "minPoolCost" .= _minPoolCost pp
      ]

instance FromJSON (PParams era) where
  parseJSON =
    Aeson.withObject "PParams" $ \obj ->
      PParams
        <$> obj .: "minFeeA"
        <*> obj .: "minFeeB"
        <*> obj .: "maxBlockBodySize"
        <*> obj .: "maxTxSize"
        <*> obj .: "maxBlockHeaderSize"
        <*> obj .: "keyDeposit"
        <*> obj .: "poolDeposit"
        <*> obj .: "eMax"
        <*> obj .: "nOpt"
        <*> ( (toRational :: Scientific -> Rational)
                <$> obj .: "a0"
            )
        <*> obj .: "rho"
        <*> obj .: "tau"
        <*> obj .: "decentralisationParam"
        <*> obj .: "extraEntropy"
        <*> obj .: "protocolVersion"
        <*> obj .:? "minUTxOValue" .!= mempty
        <*> obj .:? "minPoolCost" .!= mempty

instance Default (PParams era) where
  def = emptyPParams

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
      _minUTxOValue = mempty,
      _minPoolCost = mempty
    }

-- | Update Proposal
data Update era
  = Update !(ProposedPPUpdates era) !EpochNo
  deriving (Generic)

deriving instance Eq (PParamsDelta era) => Eq (Update era)

deriving instance NFData (PParamsDelta era) => NFData (Update era)

deriving instance Show (PParamsDelta era) => Show (Update era)

instance NoThunks (PParamsDelta era) => NoThunks (Update era)

instance (Era era, ToCBOR (PParamsDelta era)) => ToCBOR (Update era) where
  toCBOR (Update ppUpdate e) =
    encodeListLen 2 <> toCBOR ppUpdate <> toCBOR e

instance
  (Era era, FromCBOR (Annotator (PParamsDelta era))) =>
  FromCBOR (Annotator (Update era))
  where
  fromCBOR = decode $ Ann (RecD Update) <*! From <*! Ann From

data PPUpdateEnv era = PPUpdateEnv SlotNo (GenDelegs era)
  deriving (Show, Eq, Generic)

instance NoThunks (PPUpdateEnv era)

type PParamsUpdate era = PParams' StrictMaybe era

deriving instance Eq (PParams' StrictMaybe era)

deriving instance Show (PParams' StrictMaybe era)

deriving instance Ord (PParams' StrictMaybe era)

deriving instance NFData (PParams' StrictMaybe era)

instance NoThunks (PParamsUpdate era)

instance (Era era) => ToCBOR (PParamsUpdate era) where
  toCBOR ppup =
    let l =
          mapMaybe
            strictMaybeToMaybe
            [ encodeMapElement 0 toCBOR =<< _minfeeA ppup,
              encodeMapElement 1 toCBOR =<< _minfeeB ppup,
              encodeMapElement 2 toCBOR =<< _maxBBSize ppup,
              encodeMapElement 3 toCBOR =<< _maxTxSize ppup,
              encodeMapElement 4 toCBOR =<< _maxBHSize ppup,
              encodeMapElement 5 toCBOR =<< _keyDeposit ppup,
              encodeMapElement 6 toCBOR =<< _poolDeposit ppup,
              encodeMapElement 7 toCBOR =<< _eMax ppup,
              encodeMapElement 8 toCBOR =<< _nOpt ppup,
              encodeMapElement 9 ratioToCBOR =<< _a0 ppup,
              encodeMapElement 10 toCBOR =<< _rho ppup,
              encodeMapElement 11 toCBOR =<< _tau ppup,
              encodeMapElement 12 toCBOR =<< _d ppup,
              encodeMapElement 13 toCBOR =<< _extraEntropy ppup,
              encodeMapElement 14 toCBOR =<< _protocolVersion ppup,
              encodeMapElement 15 toCBOR =<< _minUTxOValue ppup,
              encodeMapElement 16 toCBOR =<< _minPoolCost ppup
            ]
        n = fromIntegral $ length l
     in encodeMapLen n <> fold l
    where
      encodeMapElement ix encoder x = SJust (encodeWord ix <> encoder x)

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
      _minUTxOValue = SNothing,
      _minPoolCost = SNothing
    }

instance (Era era) => FromCBOR (PParamsUpdate era) where
  fromCBOR = do
    mapParts <-
      decodeMapContents $
        decodeWord >>= \case
          0 -> fromCBOR >>= \x -> pure (0, \up -> up {_minfeeA = SJust x})
          1 -> fromCBOR >>= \x -> pure (1, \up -> up {_minfeeB = SJust x})
          2 -> fromCBOR >>= \x -> pure (2, \up -> up {_maxBBSize = SJust x})
          3 -> fromCBOR >>= \x -> pure (3, \up -> up {_maxTxSize = SJust x})
          4 -> fromCBOR >>= \x -> pure (4, \up -> up {_maxBHSize = SJust x})
          5 -> fromCBOR >>= \x -> pure (5, \up -> up {_keyDeposit = SJust x})
          6 -> fromCBOR >>= \x -> pure (6, \up -> up {_poolDeposit = SJust x})
          7 -> fromCBOR >>= \x -> pure (7, \up -> up {_eMax = SJust x})
          8 -> fromCBOR >>= \x -> pure (8, \up -> up {_nOpt = SJust x})
          9 -> ratioFromCBOR >>= \x -> pure (9, \up -> up {_a0 = SJust x})
          10 -> fromCBOR >>= \x -> pure (10, \up -> up {_rho = SJust x})
          11 -> fromCBOR >>= \x -> pure (11, \up -> up {_tau = SJust x})
          12 -> fromCBOR >>= \x -> pure (12, \up -> up {_d = SJust x})
          13 -> fromCBOR >>= \x -> pure (13, \up -> up {_extraEntropy = SJust x})
          14 -> fromCBOR >>= \x -> pure (14, \up -> up {_protocolVersion = SJust x})
          15 -> fromCBOR >>= \x -> pure (15, \up -> up {_minUTxOValue = SJust x})
          16 -> fromCBOR >>= \x -> pure (16, \up -> up {_minPoolCost = SJust x})
          k -> invalidKey k
    let fields = fst <$> mapParts :: [Int]
    unless
      (nub fields == fields)
      (fail $ "duplicate keys: " <> show fields)
    pure $ foldr ($) emptyPParamsUpdate (snd <$> mapParts)

instance Era era => FromCBOR (Annotator (PParamsUpdate era)) where
  fromCBOR = pure <$> fromCBOR

-- | Update operation for protocol parameters structure @PParams
newtype ProposedPPUpdates era
  = ProposedPPUpdates (Map (KeyHash 'Genesis (Crypto era)) (PParamsDelta era))
  deriving (Generic)

deriving instance Eq (PParamsDelta era) => Eq (ProposedPPUpdates era)

deriving instance NFData (PParamsDelta era) => NFData (ProposedPPUpdates era)

deriving instance Show (PParamsDelta era) => Show (ProposedPPUpdates era)

instance NoThunks (PParamsDelta era) => NoThunks (ProposedPPUpdates era)

instance
  (Era era, ToCBOR (PParamsDelta era)) =>
  ToCBOR (ProposedPPUpdates era)
  where
  toCBOR (ProposedPPUpdates m) = mapToCBOR m

instance
  (Era era, FromCBOR (Annotator (PParamsDelta era))) =>
  FromCBOR (Annotator (ProposedPPUpdates era))
  where
  fromCBOR =
    decode $
      Ann (Emit ProposedPPUpdates)
        <*! mapDecodeA (Ann From) From

instance
  (Era era, FromCBOR (PParamsDelta era)) =>
  FromCBOR (ProposedPPUpdates era)
  where
  fromCBOR = ProposedPPUpdates <$> mapFromCBOR

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
      _minUTxOValue = fromMaybe' (_minUTxOValue pp) (_minUTxOValue ppup),
      _minPoolCost = fromMaybe' (_minPoolCost pp) (_minPoolCost ppup)
    }
  where
    fromMaybe' :: a -> StrictMaybe a -> a
    fromMaybe' x = fromMaybe x . strictMaybeToMaybe
