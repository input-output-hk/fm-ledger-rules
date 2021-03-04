{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE EmptyDataDeriving #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}
-- This is needed to make Plutus.Data instances
{-# OPTIONS_GHC -fno-warn-orphans #-}

module Cardano.Ledger.Alonzo.Data
  ( Data (Data, ..),
    DataHash,
    hashData,
    -- $
    AuxiliaryData (AuxiliaryData, scripts, dats, txMD),
    AuxiliaryDataHash (..),
    -- $
    ppPlutusData,
    ppData,
    ppAuxiliaryData,
  )
where

import Cardano.Binary (FromCBOR (..), ToCBOR (..))
import Cardano.Ledger.AuxiliaryData (AuxiliaryDataHash (..))
import qualified Cardano.Ledger.Core as Core
import Cardano.Ledger.Era (Crypto, Era)
import Cardano.Ledger.Pretty
  ( PDoc,
    PrettyA (..),
    ppInteger,
    ppList,
    ppLong,
    ppMetadata,
    ppPair,
    ppSet,
    ppSexp,
  )
import Cardano.Ledger.SafeHash
  ( EraIndependentAuxiliaryData,
    EraIndependentData,
    HashAnnotated,
    SafeHash,
    SafeToHash,
    hashAnnotated,
  )
import Data.Coders
import Data.MemoBytes (Mem, MemoBytes (..), memoBytes)
import Data.Set (Set)
import Data.Typeable (Typeable)
import GHC.Generics (Generic)
-- import Plutus.V1.Ledger.Scripts
import qualified Language.PlutusTx as Plutus
import NoThunks.Class (InspectHeapNamed (..), NoThunks)
import Shelley.Spec.Ledger.Metadata (Metadata)

-- =====================================================================
-- Plutus.Data is the type that Plutus expects as data.
-- It is imported from the Plutus package, but it needs a few additional
-- instances to also work in the ledger.

instance FromCBOR (Annotator Plutus.Data) where
  fromCBOR = decode (Summands "PlutusData" decPlutus)
    where
      decPlutus :: Word -> Decode 'Open (Annotator Plutus.Data)
      decPlutus 0 = Ann (SumD Plutus.Constr) <*! (Ann From) <*! listDecodeA From
      decPlutus 1 = Ann (SumD Plutus.Map) <*! listDecodeA (pairDecodeA From From)
      decPlutus 2 = Ann (SumD Plutus.List) <*! listDecodeA From
      decPlutus 3 = Ann (SumD Plutus.I <! From)
      decPlutus 4 = Ann (SumD Plutus.B <! From)
      decPlutus n = Invalid n

instance ToCBOR Plutus.Data where
  toCBOR x = encode (encPlutus x)
    where
      encPlutus (Plutus.Constr tag args) = Sum Plutus.Constr 0 !> To tag !> listEncode args
      encPlutus (Plutus.Map pairs) = Sum Plutus.Map 1 !> listEncode pairs
      encPlutus (Plutus.List xs) = Sum Plutus.List 2 !> listEncode xs
      encPlutus (Plutus.I i) = Sum Plutus.I 3 !> To i
      encPlutus (Plutus.B bytes) = Sum Plutus.B 4 !> To bytes

deriving instance NoThunks Plutus.Data

-- ============================================================================
-- the newtype Data is a wrapper around the type that Plutus expects as data.
-- The newtype will memoize the serialized bytes.

newtype Data era = DataConstr (MemoBytes Plutus.Data)
  deriving (Eq, Ord, Generic, Show)
  deriving newtype (SafeToHash, ToCBOR)

deriving via
  (Mem Plutus.Data)
  instance
    (Era era) =>
    FromCBOR (Annotator (Data era))

instance (Crypto era ~ c) => HashAnnotated (Data era) EraIndependentData c

instance NoThunks (Data era)

pattern Data :: Plutus.Data -> Data era
pattern Data p <-
  DataConstr (Memo p _)
  where
    Data p = DataConstr (memoBytes (To p))

-- =============================================================================

type DataHash crypto = SafeHash crypto EraIndependentData

hashData :: Era era => Data era -> DataHash (Crypto era)
hashData d = hashAnnotated d

-- =============================================================================
-- Version without serialized bytes

data AuxiliaryDataRaw era = AuxiliaryDataRaw
  { scripts' :: Set (Core.Script era),
    dats' :: Set (Data era),
    txMD' :: Set (Metadata era)
  }
  deriving (Generic)

deriving instance Eq (Core.Script era) => Eq (AuxiliaryDataRaw era)

deriving instance Show (Core.Script era) => Show (AuxiliaryDataRaw era)

deriving via InspectHeapNamed "AuxiliaryDataRaw" (AuxiliaryDataRaw era) instance NoThunks (AuxiliaryDataRaw era)

instance
  ( Typeable era,
    Ord (Core.Script era),
    ToCBOR (Core.Script era)
  ) =>
  ToCBOR (AuxiliaryDataRaw era)
  where
  toCBOR (AuxiliaryDataRaw s d m) =
    encode (encodeRaw s d m)

encodeRaw ::
  (ToCBOR (Core.Script era), Typeable era) =>
  Set (Core.Script era) ->
  Set (Data era) ->
  Set (Metadata era) ->
  Encode ('Closed 'Dense) (AuxiliaryDataRaw era)
encodeRaw s d m =
  ( Rec AuxiliaryDataRaw
      !> setEncode s
      !> setEncode d
      !> setEncode m
  )

instance
  ( Era era,
    Ord (Core.Script era),
    FromCBOR (Annotator (Core.Script era))
  ) =>
  FromCBOR (Annotator (AuxiliaryDataRaw era))
  where
  fromCBOR =
    decode
      ( Ann (RecD AuxiliaryDataRaw)
          <*! setDecodeA From
          <*! setDecodeA From
          <*! setDecodeA From
      )

-- ================================================================================
-- Version with serialized bytes.

newtype AuxiliaryData era = AuxiliaryDataConstr (MemoBytes (AuxiliaryDataRaw era))
  deriving newtype (ToCBOR, SafeToHash)

instance (Crypto era ~ c) => HashAnnotated (AuxiliaryData era) EraIndependentAuxiliaryData c

deriving instance Eq (Core.Script era) => Eq (AuxiliaryData era)

deriving instance Show (Core.Script era) => Show (AuxiliaryData era)

deriving via InspectHeapNamed "AuxiliaryDataRaw" (AuxiliaryData era) instance NoThunks (AuxiliaryData era)

deriving via
  (Mem (AuxiliaryDataRaw era))
  instance
    ( Era era,
      Ord (Core.Script era),
      FromCBOR (Annotator (Core.Script era))
    ) =>
    FromCBOR (Annotator (AuxiliaryData era))

pattern AuxiliaryData ::
  (Era era, ToCBOR (Core.Script era), Ord (Core.Script era)) =>
  Set (Core.Script era) ->
  Set (Data era) ->
  Set (Metadata era) ->
  AuxiliaryData era
pattern AuxiliaryData {scripts, dats, txMD} <-
  AuxiliaryDataConstr (Memo (AuxiliaryDataRaw scripts dats txMD) _)
  where
    AuxiliaryData s d m =
      AuxiliaryDataConstr
        ( memoBytes
            (encodeRaw s d m)
        )

{-# COMPLETE AuxiliaryData #-}

-- =======================================================

ppPlutusData :: Plutus.Data -> PDoc
ppPlutusData (Plutus.Constr tag args) = ppSexp "Constr" [ppInteger tag, ppList ppPlutusData args]
ppPlutusData (Plutus.Map pairs) = ppSexp "Map" [ppList (ppPair ppPlutusData ppPlutusData) pairs]
ppPlutusData (Plutus.List xs) = ppSexp "List" [ppList ppPlutusData xs]
ppPlutusData (Plutus.I i) = ppSexp "I" [ppInteger i]
ppPlutusData (Plutus.B bytes) = ppSexp "B" [ppLong bytes]

instance PrettyA Plutus.Data where prettyA = ppPlutusData

ppData :: Data era -> PDoc
ppData (DataConstr (Memo x _)) = ppSexp "Data" [ppPlutusData x]

instance PrettyA (Data era) where prettyA = ppData

ppAuxiliaryData :: (PrettyA (Core.Script era)) => AuxiliaryData era -> PDoc
ppAuxiliaryData (AuxiliaryDataConstr (Memo (AuxiliaryDataRaw s d m) _)) =
  ppSexp "AuxiliaryData" [ppSet prettyA s, ppSet ppData d, ppSet ppMetadata m]

instance (PrettyA (Core.Script era)) => PrettyA (AuxiliaryData era) where prettyA = ppAuxiliaryData
