{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}

module Shelley.Spec.Ledger.Tx
  ( -- transaction
    Tx
      ( Tx,
        Tx',
        _body,
        _witnessSet,
        _metadata,
        TxPrime,
        body',
        witnessSet',
        metadata',
        txFullBytes
      ),
    TxBody (..),
    TxOut (..),
    TxIn (..),
    TxId (..),
    decodeWits,
    segwitTx,
    -- witness data
    WitnessSet,
    WitnessSetHKD
      ( WitnessSet,
        addrWits,
        bootWits,
        scriptWits,
        txWitsBytes
      ),
    WitVKey (..),
    ValidateScript (..),
    txwitsScript,
    extractKeyHashWitnessSet,
    addrWits',
    evalNativeMultiSigScript,
    hashMultiSigScript,
    validateNativeMultiSigScript,
    TransTx,
    TransWitnessSet,
    prettyWitnessSetParts,
  )
where

import Cardano.Binary
  ( Annotator (..),
    Decoder,
    FromCBOR (fromCBOR),
    ToCBOR (toCBOR),
    annotatorSlice,
    decodeWord,
    encodeListLen,
    encodeMapLen,
    encodeNull,
    encodePreEncoded,
    encodeWord,
    serialize,
    serializeEncoding,
    withSlice,
  )
import qualified Cardano.Ledger.Core as Core
import qualified Cardano.Ledger.Crypto as CC (Crypto)
import Cardano.Ledger.Era
import Cardano.Ledger.SafeHash (EraIndependentTx, HashAnnotated, SafeToHash (..))
import qualified Data.ByteString.Lazy as BSL
import Data.Constraint (Constraint)
import Data.Foldable (fold)
import Data.Functor.Identity (Identity)
import Data.Kind (Type)
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Data.Maybe (catMaybes)
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Typeable
import GHC.Generics (Generic)
import GHC.Records (HasField (..))
import NoThunks.Class (AllowThunksIn (..), NoThunks (..))
import Shelley.Spec.Ledger.Address.Bootstrap (BootstrapWitness)
import Shelley.Spec.Ledger.BaseTypes
  ( StrictMaybe,
    invalidKey,
    maybeToStrictMaybe,
    strictMaybeToMaybe,
  )
import Shelley.Spec.Ledger.Credential (Credential (..))
import Shelley.Spec.Ledger.Keys
import Shelley.Spec.Ledger.Scripts
import Shelley.Spec.Ledger.Serialization
  ( decodeList,
    decodeMapContents,
    decodeNullMaybe,
    decodeRecordNamed,
    encodeFoldable,
    encodeNullMaybe,
  )
import Shelley.Spec.Ledger.TxBody
  ( TxBody (..),
    TxId (..),
    TxIn (..),
    TxOut (..),
    WitVKey (..),
    witKeyHash,
  )

-- ========================================================

-- | Higher Kinded Data
type family HKD f a where
  HKD Identity a = a
  HKD f a = f a

data WitnessSetHKD f era = WitnessSet'
  { addrWits' :: !(HKD f (Set (WitVKey 'Witness (Crypto era)))),
    scriptWits' :: !(HKD f (Map (ScriptHash (Crypto era)) (Core.Script era))),
    bootWits' :: !(HKD f (Set (BootstrapWitness (Crypto era)))),
    txWitsBytes :: BSL.ByteString
  }

type TransWitnessSet (c :: Type -> Constraint) era = c (Core.Script era)

deriving instance
  (Era era, TransWitnessSet Show era) =>
  Show (WitnessSetHKD Identity era)

deriving instance
  (Era era, TransWitnessSet Eq era) =>
  Eq (WitnessSetHKD Identity era)

deriving instance Era era => Generic (WitnessSetHKD Identity era)

deriving via
  AllowThunksIn
    '[ "txWitsBytes"
     ]
    (WitnessSetHKD Identity era)
  instance
    (Era era, TransWitnessSet NoThunks era) =>
    (NoThunks (WitnessSetHKD Identity era))

type WitnessSet = WitnessSetHKD Identity

instance Era era => ToCBOR (WitnessSetHKD Identity era) where
  toCBOR = encodePreEncoded . BSL.toStrict . txWitsBytes

instance
  (Era era, Core.AnnotatedData (Core.Script era)) =>
  Semigroup (WitnessSetHKD Identity era)
  where
  (WitnessSet a b c) <> (WitnessSet a' b' c') =
    WitnessSet (a <> a') (b <> b') (c <> c')

instance
  (Era era, Core.AnnotatedData (Core.Script era)) =>
  Monoid (WitnessSetHKD Identity era)
  where
  mempty = WitnessSet mempty mempty mempty

pattern WitnessSet ::
  (Era era, Core.AnnotatedData (Core.Script era)) =>
  Set (WitVKey 'Witness (Crypto era)) ->
  Map (ScriptHash (Crypto era)) (Core.Script era) ->
  Set (BootstrapWitness (Crypto era)) ->
  WitnessSet era
pattern WitnessSet {addrWits, scriptWits, bootWits} <-
  WitnessSet' addrWits scriptWits bootWits _
  where
    WitnessSet awits scriptWitMap bootstrapWits =
      let encodeMapElement ix enc x =
            if null x then Nothing else Just (encodeWord ix <> enc x)
          l =
            catMaybes $
              [ encodeMapElement 0 encodeFoldable awits,
                encodeMapElement 1 encodeFoldable scriptWitMap,
                encodeMapElement 2 encodeFoldable bootstrapWits
              ]
          n = fromIntegral $ length l
          witsBytes = serializeEncoding $ encodeMapLen n <> fold l
       in WitnessSet'
            { addrWits' = awits,
              scriptWits' = scriptWitMap,
              bootWits' = bootstrapWits,
              txWitsBytes = witsBytes
            }

{-# COMPLETE WitnessSet #-}

-- | Exports the relevant parts from a (WintessSetHKD Identity era) for
--     use by the pretty printer without all the horrible constraints.
--     Uses the non-exported WitnessSet' constructor.
prettyWitnessSetParts ::
  WitnessSetHKD Identity era ->
  ( Set (WitVKey 'Witness (Crypto era)),
    Map (ScriptHash (Crypto era)) (Core.Script era),
    Set (BootstrapWitness (Crypto era))
  )
prettyWitnessSetParts (WitnessSet' a b c _) = (a, b, c)

-- | A fully formed transaction.
data Tx era = Tx'
  { _bodyS :: !(Core.TxBody era),
    _witnessSetS :: !(WitnessSet era),
    _metadataS :: !(StrictMaybe (Core.AuxiliaryData era)),
    txFullBytes :: BSL.ByteString
  }
  deriving (Generic)

-- Usually we derive SafetToHash instances, but since (Tx era) preserves its serialisation
-- bytes we can just extract them here, and make an explicit SafeToHash instance.

instance SafeToHash (Tx era) where
  originalBytes = BSL.toStrict . txFullBytes -- TODO Use MemoBytes to define Tx, so we can derive this

type TransTx (c :: Type -> Constraint) era =
  (Era era, c (Core.Script era), c (Core.TxBody era), c (Core.AuxiliaryData era))

deriving via
  AllowThunksIn
    '[ "txFullBytes"
     ]
    (Tx era)
  instance
    (TransTx NoThunks era) => NoThunks (Tx era)

deriving instance
  TransTx Show era =>
  Show (Tx era)

deriving instance
  TransTx Eq era =>
  Eq (Tx era)

pattern TxPrime ::
  Core.TxBody era ->
  WitnessSet era ->
  StrictMaybe (Core.AuxiliaryData era) ->
  Tx era
pattern TxPrime {body', witnessSet', metadata'} <-
  Tx' body' witnessSet' metadata' _

{-# COMPLETE TxPrime #-}

pattern Tx ::
  TransTx ToCBOR era =>
  Core.TxBody era ->
  WitnessSet era ->
  StrictMaybe (Core.AuxiliaryData era) ->
  Tx era
pattern Tx {_body, _witnessSet, _metadata} <-
  Tx' _body _witnessSet _metadata _
  where
    Tx body witnessSet metadata =
      let bodyBytes = serialize body
          wrappedMetadataBytes =
            serializeEncoding $
              encodeNullMaybe toCBOR (strictMaybeToMaybe metadata)
          fullBytes =
            (serializeEncoding $ encodeListLen 3)
              <> bodyBytes
              <> serialize witnessSet
              <> wrappedMetadataBytes
       in Tx'
            { _bodyS = body,
              _witnessSetS = witnessSet,
              _metadataS = metadata,
              txFullBytes = fullBytes
            }

{-# COMPLETE Tx #-}

-- =====================================
-- WellFormed instances

instance (Era era, c ~ Crypto era) => HashAnnotated (Tx era) EraIndependentTx c

instance body ~ (Core.TxBody era) => HasField "body" (Tx era) body where
  getField (Tx' body _ _ _) = body

instance HasField "witnessSet" (Tx era) (WitnessSet era) where
  getField (Tx' _ wits _ _) = wits

instance
  aux ~ Core.AuxiliaryData era =>
  HasField "auxiliaryData" (Tx era) (StrictMaybe aux)
  where
  getField (Tx' _ _ auxdata _) = auxdata

instance
  c ~ (Crypto era) =>
  HasField "addrWits" (Tx era) (Set (WitVKey 'Witness c))
  where
  getField (Tx' _ (WitnessSet' a _b _c _) _ _) = a

instance
  (c ~ (Crypto era), script ~ Core.Script era) =>
  HasField "scriptWits" (Tx era) (Map (ScriptHash c) script)
  where
  getField (Tx' _ (WitnessSet' _a b _c _) _ _) = b

instance
  c ~ (Crypto era) =>
  HasField "bootWits" (Tx era) (Set (BootstrapWitness c))
  where
  getField (Tx' _ (WitnessSet' _a _b c _) _ _) = c

instance HasField "txsize" (Tx era) Integer where
  getField x = (fromIntegral . BSL.length . txFullBytes) x

-- =====================================

segwitTx ::
  ( Era era,
    ToCBOR (Core.TxBody era),
    ToCBOR (Core.AuxiliaryData era)
  ) =>
  Annotator (Core.TxBody era) ->
  Annotator (WitnessSet era) ->
  Maybe (Annotator (Core.AuxiliaryData era)) ->
  Annotator (Tx era)
segwitTx
  bodyAnn
  witsAnn
  metaAnn = Annotator $ \bytes ->
    let body = runAnnotator bodyAnn bytes
        witnessSet = runAnnotator witsAnn bytes
        metadata = flip runAnnotator bytes <$> metaAnn
        wrappedMetadataBytes = case metadata of
          Nothing -> serializeEncoding encodeNull
          Just b -> serialize b
        fullBytes =
          (serializeEncoding $ encodeListLen 3)
            <> serialize body
            <> serialize witnessSet
            <> wrappedMetadataBytes
     in Tx'
          { _bodyS = body,
            _witnessSetS = witnessSet,
            _metadataS = maybeToStrictMaybe metadata,
            txFullBytes = fullBytes
          }

decodeWits ::
  forall era s.
  ( Core.AnnotatedData (Core.Script era),
    ValidateScript era
  ) =>
  Decoder s (Annotator (WitnessSet era))
decodeWits = do
  (mapParts, annBytes) <-
    withSlice $
      decodeMapContents $
        decodeWord >>= \case
          0 ->
            decodeList fromCBOR >>= \x ->
              pure (\ws -> ws {addrWits' = Set.fromList <$> sequence x})
          1 ->
            decodeList fromCBOR >>= \x ->
              pure (\ws -> ws {scriptWits' = keyBy (hashScript @era) <$> sequence x})
          2 ->
            decodeList fromCBOR >>= \x ->
              pure (\ws -> ws {bootWits' = Set.fromList <$> sequence x})
          k -> invalidKey k
  let witSet = foldr ($) emptyWitnessSetHKD mapParts
      emptyWitnessSetHKD :: WitnessSetHKD Annotator era
      emptyWitnessSetHKD =
        WitnessSet'
          { addrWits' = pure mempty,
            scriptWits' = pure mempty,
            bootWits' = pure mempty,
            txWitsBytes = mempty
          }
  pure $
    WitnessSet'
      <$> addrWits' witSet
      <*> scriptWits' witSet
      <*> bootWits' witSet
      <*> annBytes

keyBy :: Ord k => (a -> k) -> [a] -> Map k a
keyBy f xs = Map.fromList $ (\x -> (f x, x)) <$> xs

instance
  Typeable era =>
  ToCBOR (Tx era)
  where
  toCBOR tx = encodePreEncoded . BSL.toStrict $ txFullBytes tx

instance
  ( FromCBOR (Annotator (Core.TxBody era)),
    ValidateScript era,
    FromCBOR (Annotator (Core.Script era)),
    FromCBOR (Annotator (Core.AuxiliaryData era))
  ) =>
  FromCBOR (Annotator (Tx era))
  where
  fromCBOR = annotatorSlice $
    decodeRecordNamed "Tx" (const 3) $ do
      body <- fromCBOR
      wits <- decodeWits
      meta <-
        ( decodeNullMaybe fromCBOR ::
            Decoder s (Maybe (Annotator (Core.AuxiliaryData era)))
          )
      pure $
        Annotator $ \fullBytes bytes ->
          Tx'
            { _bodyS = runAnnotator body fullBytes,
              _witnessSetS = runAnnotator wits fullBytes,
              _metadataS = maybeToStrictMaybe $ flip runAnnotator fullBytes <$> meta,
              txFullBytes = bytes
            }

-- | Typeclass for multis-signature script data types. Allows for script
-- validation and hashing.
class
  (Era era, ToCBOR (Core.Script era)) =>
  ValidateScript era
  where
  validateScript :: Core.Script era -> Core.Tx era -> Bool
  hashScript :: Core.Script era -> ScriptHash (Crypto era)
  isNativeScript :: Core.Script era -> Bool
  isNativeScript _ = True

-- | Script evaluator for native multi-signature scheme. 'vhks' is the set of
-- key hashes that signed the transaction to be validated.
evalNativeMultiSigScript ::
  CC.Crypto crypto =>
  MultiSig crypto ->
  Set (KeyHash 'Witness crypto) ->
  Bool
evalNativeMultiSigScript (RequireSignature hk) vhks = Set.member hk vhks
evalNativeMultiSigScript (RequireAllOf msigs) vhks =
  all (`evalNativeMultiSigScript` vhks) msigs
evalNativeMultiSigScript (RequireAnyOf msigs) vhks =
  any (`evalNativeMultiSigScript` vhks) msigs
evalNativeMultiSigScript (RequireMOf m msigs) vhks =
  m <= sum [if evalNativeMultiSigScript msig vhks then 1 else 0 | msig <- msigs]

-- | Script validator for native multi-signature scheme.
validateNativeMultiSigScript ::
  TransTx ToCBOR era =>
  MultiSig (Crypto era) ->
  Tx era ->
  Bool
validateNativeMultiSigScript msig tx =
  evalNativeMultiSigScript msig (coerceKeyRole `Set.map` vhks)
  where
    witsSet = _witnessSet tx
    vhks = Set.map witKeyHash (addrWits' witsSet)

-- | Multi-signature script witness accessor function for Transactions
txwitsScript ::
  TransTx ToCBOR era =>
  Tx era ->
  Map (ScriptHash (Crypto era)) (Core.Script era)
txwitsScript = scriptWits' . _witnessSet

extractKeyHashWitnessSet ::
  forall (r :: KeyRole) crypto.
  [Credential r crypto] ->
  Set (KeyHash 'Witness crypto)
extractKeyHashWitnessSet credentials = foldr accum Set.empty credentials
  where
    accum (KeyHashObj hk) ans = Set.insert (asWitness hk) ans
    accum _other ans = ans
