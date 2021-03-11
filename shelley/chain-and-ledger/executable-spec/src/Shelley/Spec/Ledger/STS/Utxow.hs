{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE EmptyDataDecls #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}

module Shelley.Spec.Ledger.STS.Utxow
  ( UTXOW,
    UtxowPredicateFailure (..),
    PredicateFailure,
    shelleyStyleWitness,
    ShelleyStyleWitnessNeeds,
    initialLedgerStateUTXOW,
  )
where

import Cardano.Binary
  ( FromCBOR (..),
    ToCBOR (..),
    encodeListLen,
  )
import Cardano.Ledger.AuxiliaryData
  ( AuxiliaryDataHash,
    ValidateAuxiliaryData (..),
    hashAuxiliaryData,
  )
import qualified Cardano.Ledger.Core as Core
import Cardano.Ledger.Era (Crypto, Era)
import Control.Monad (when)
import Control.Monad.Trans.Reader (asks)
import Control.SetAlgebra (eval, (∩))
import Control.State.Transition
  ( Embed,
    IRC (..),
    InitialRule,
    STS (..),
    TRC (..),
    TransitionRule,
    failBecause,
    judgmentContext,
    liftSTS,
    trans,
    wrapFailed,
    (?!),
    (?!:),
  )
import qualified Data.Map.Strict as Map
import qualified Data.Sequence as Seq (filter)
import Data.Sequence.Strict (StrictSeq)
import qualified Data.Sequence.Strict as StrictSeq
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Typeable (Typeable)
import Data.Word (Word8)
import GHC.Generics (Generic)
import GHC.Records (HasField, getField)
import NoThunks.Class (NoThunks (..))
import Shelley.Spec.Ledger.BaseTypes
  ( ShelleyBase,
    StrictMaybe (..),
    invalidKey,
    quorum,
    (==>),
  )
import Shelley.Spec.Ledger.Delegation.Certificates (isInstantaneousRewards)
import Shelley.Spec.Ledger.Keys
  ( DSignable,
    GenDelegPair (..),
    GenDelegs (..),
    Hash,
    KeyHash,
    KeyRole (..),
    VKey,
    asWitness,
  )
import Shelley.Spec.Ledger.LedgerState
  ( UTxOState (..),
    WitHashes (..),
    diffWitHashes,
    nullWitHashes,
    verifiedWits,
    witsFromTxWitnesses,
    witsVKeyNeeded,
  )
import Shelley.Spec.Ledger.PParams (ProtVer, Update)
import Shelley.Spec.Ledger.STS.Utxo (UTXO, UtxoEnv (..), UtxoPredicateFailure)
import Shelley.Spec.Ledger.Scripts (ScriptHash)
import Shelley.Spec.Ledger.Serialization
  ( decodeList,
    decodeRecordSum,
    decodeSet,
    encodeFoldable,
  )
import qualified Shelley.Spec.Ledger.SoftForks as SoftForks
import Shelley.Spec.Ledger.Tx (Tx (..), ValidateScript, WitVKey, hashScript, validateScript)
import Shelley.Spec.Ledger.TxBody (DCert, EraIndependentTxBody, TxIn, Wdrl)
import Shelley.Spec.Ledger.UTxO (scriptsNeeded)

-- =========================================

data UTXOW era

data UtxowPredicateFailure era
  = InvalidWitnessesUTXOW
      ![VKey 'Witness (Crypto era)]
  | -- witnesses which failed in verifiedWits function
    MissingVKeyWitnessesUTXOW
      !(WitHashes (Crypto era)) -- witnesses which were needed and not supplied
  | MissingScriptWitnessesUTXOW
      !(Set (ScriptHash (Crypto era))) -- missing scripts
  | ScriptWitnessNotValidatingUTXOW
      !(Set (ScriptHash (Crypto era))) -- failed scripts
  | UtxoFailure (PredicateFailure (Core.EraRule "UTXO" era))
  | MIRInsufficientGenesisSigsUTXOW (Set (KeyHash 'Witness (Crypto era)))
  | MissingTxBodyMetadataHash
      !(AuxiliaryDataHash (Crypto era)) -- hash of the full metadata
  | MissingTxMetadata
      !(AuxiliaryDataHash (Crypto era)) -- hash of the metadata included in the transaction body
  | ConflictingMetadataHash
      !(AuxiliaryDataHash (Crypto era)) -- hash of the metadata included in the transaction body
      !(AuxiliaryDataHash (Crypto era)) -- hash of the full metadata
      -- Contains out of range values (strings too long)
  | InvalidMetadata
  deriving (Generic)

instance
  ( NoThunks (PredicateFailure (Core.EraRule "UTXO" era)),
    Era era
  ) =>
  NoThunks (UtxowPredicateFailure era)

deriving stock instance
  ( Eq (PredicateFailure (Core.EraRule "UTXO" era)),
    Era era
  ) =>
  Eq (UtxowPredicateFailure era)

deriving stock instance
  ( Show (PredicateFailure (Core.EraRule "UTXO" era)),
    Era era
  ) =>
  Show (UtxowPredicateFailure era)

instance
  ( Era era,
    Typeable (Core.Script era),
    Typeable (Core.AuxiliaryData era),
    ToCBOR (PredicateFailure (Core.EraRule "UTXO" era))
  ) =>
  ToCBOR (UtxowPredicateFailure era)
  where
  toCBOR = \case
    InvalidWitnessesUTXOW wits ->
      encodeListLen 2 <> toCBOR (0 :: Word8) <> encodeFoldable wits
    MissingVKeyWitnessesUTXOW (WitHashes missing) ->
      encodeListLen 2 <> toCBOR (1 :: Word8) <> encodeFoldable missing
    MissingScriptWitnessesUTXOW ss ->
      encodeListLen 2 <> toCBOR (2 :: Word8)
        <> encodeFoldable ss
    ScriptWitnessNotValidatingUTXOW ss ->
      encodeListLen 2 <> toCBOR (3 :: Word8)
        <> encodeFoldable ss
    (UtxoFailure a) ->
      encodeListLen 2 <> toCBOR (4 :: Word8)
        <> toCBOR a
    MIRInsufficientGenesisSigsUTXOW sigs ->
      encodeListLen 2 <> toCBOR (5 :: Word8)
        <> encodeFoldable sigs
    MissingTxBodyMetadataHash h ->
      encodeListLen 2 <> toCBOR (6 :: Word8) <> toCBOR h
    MissingTxMetadata h ->
      encodeListLen 2 <> toCBOR (7 :: Word8) <> toCBOR h
    ConflictingMetadataHash bodyHash fullMDHash ->
      encodeListLen 3 <> toCBOR (8 :: Word8) <> toCBOR bodyHash <> toCBOR fullMDHash
    InvalidMetadata ->
      encodeListLen 1 <> toCBOR (9 :: Word8)

instance
  ( Era era,
    FromCBOR (PredicateFailure (Core.EraRule "UTXO" era)),
    Typeable (Core.Script era),
    Typeable (Core.AuxiliaryData era)
  ) =>
  FromCBOR (UtxowPredicateFailure era)
  where
  fromCBOR = decodeRecordSum "PredicateFailure (UTXOW era)" $
    \case
      0 -> do
        wits <- decodeList fromCBOR
        pure (2, InvalidWitnessesUTXOW wits)
      1 -> do
        missing <- decodeSet fromCBOR
        pure (2, MissingVKeyWitnessesUTXOW $ WitHashes missing)
      2 -> do
        ss <- decodeSet fromCBOR
        pure (2, MissingScriptWitnessesUTXOW ss)
      3 -> do
        ss <- decodeSet fromCBOR
        pure (2, ScriptWitnessNotValidatingUTXOW ss)
      4 -> do
        a <- fromCBOR
        pure (2, UtxoFailure a)
      5 -> do
        s <- decodeSet fromCBOR
        pure (2, MIRInsufficientGenesisSigsUTXOW s)
      6 -> do
        h <- fromCBOR
        pure (2, MissingTxBodyMetadataHash h)
      7 -> do
        h <- fromCBOR
        pure (2, MissingTxMetadata h)
      8 -> do
        bodyHash <- fromCBOR
        fullMDHash <- fromCBOR
        pure (3, ConflictingMetadataHash bodyHash fullMDHash)
      9 -> pure (1, InvalidMetadata)
      k -> invalidKey k

-- =================================================
--  State Transition System Instances

type ShelleyStyleWitnessNeeds era =
  ( HasField "certs" (Core.TxBody era) (StrictSeq (DCert (Crypto era))),
    HasField "inputs" (Core.TxBody era) (Set (TxIn (Crypto era))),
    HasField "wdrls" (Core.TxBody era) (Wdrl (Crypto era)),
    HasField "addrWits" (Core.Tx era) (Set (WitVKey 'Witness (Crypto era))),
    HasField "update" (Core.TxBody era) (StrictMaybe (Update era)),
    HasField "_protocolVersion" (Core.PParams era) ProtVer,
    ValidateAuxiliaryData era (Crypto era),
    ValidateScript era,
    DSignable (Crypto era) (Hash (Crypto era) EraIndependentTxBody)
  )

initialLedgerStateUTXOW ::
  forall era.
  ( Embed (Core.EraRule "UTXO" era) (UTXOW era),
    Environment (Core.EraRule "UTXO" era) ~ UtxoEnv era,
    State (Core.EraRule "UTXO" era) ~ UTxOState era
  ) =>
  InitialRule (UTXOW era)
initialLedgerStateUTXOW = do
  IRC (UtxoEnv slots pp stakepools genDelegs) <- judgmentContext
  trans @(Core.EraRule "UTXO" era) $ IRC (UtxoEnv slots pp stakepools genDelegs)

-- | A generic Utxow witnessing function designed to be use across many Eras.
--   Note the 'embed' argument lifts from the simple Shelley (UtxowPredicateFailure) to
--   the PredicateFailure (type family) of the context of where it is called.
shelleyStyleWitness ::
  forall era utxow.
  ( Era era,
    BaseM (utxow era) ~ ShelleyBase,
    Embed (Core.EraRule "UTXO" era) (utxow era),
    Environment (Core.EraRule "UTXO" era) ~ UtxoEnv era,
    State (Core.EraRule "UTXO" era) ~ UTxOState era,
    Signal (Core.EraRule "UTXO" era) ~ Core.Tx era,
    Environment (utxow era) ~ UtxoEnv era,
    State (utxow era) ~ UTxOState era,
    Signal (utxow era) ~ Core.Tx era,
    -- PredicateFailure (utxow era) ~ UtxowPredicateFailure era,
    STS (utxow era),
    ShelleyStyleWitnessNeeds era
  ) =>
  (UtxowPredicateFailure era -> PredicateFailure (utxow era)) ->
  TransitionRule (utxow era)
shelleyStyleWitness embed = do
  (TRC (UtxoEnv slot pp stakepools genDelegs, u, tx)) <- judgmentContext
  let txbody = getField @"body" tx
      utxo = _utxo u
      witsKeyHashes = witsFromTxWitnesses @era tx
      auxdata = getField @"auxiliaryData" tx

  -- check scripts
  let failedScripts =
        filter
          ( \(hs, validator) ->
              hashScript @era validator /= hs
                || not (validateScript @era validator tx)
          )
          (Map.toList $ (getField @"scriptWits" tx))
  case failedScripts of
    [] -> pure ()
    fs -> failBecause $ embed $ ScriptWitnessNotValidatingUTXOW $ Set.fromList $ fmap fst fs

  let sNeeded = scriptsNeeded utxo tx
      sReceived = Map.keysSet (getField @"scriptWits" tx)
  sNeeded == sReceived
    ?! embed (MissingScriptWitnessesUTXOW (sNeeded `Set.difference` sReceived))

  -- check VKey witnesses
  verifiedWits @era tx ?!: (embed . InvalidWitnessesUTXOW)

  let needed = witsVKeyNeeded @era utxo tx genDelegs
      missingWitnesses = diffWitHashes needed witsKeyHashes
      haveNeededWitnesses = case nullWitHashes missingWitnesses of
        True -> Right ()
        False -> Left missingWitnesses
  haveNeededWitnesses ?!: (embed . MissingVKeyWitnessesUTXOW)

  -- check metadata hash
  case (getField @"adHash" txbody, auxdata) of
    (SNothing, SNothing) -> pure ()
    (SJust mdh, SNothing) -> failBecause $ (embed (MissingTxMetadata mdh))
    (SNothing, SJust md') ->
      failBecause $
        embed (MissingTxBodyMetadataHash (hashAuxiliaryData @era md'))
    (SJust mdh, SJust md') -> do
      hashAuxiliaryData @era md' == mdh
        ?! (embed (ConflictingMetadataHash mdh (hashAuxiliaryData @era md')))

      -- check metadata value sizes
      when (SoftForks.validMetadata pp) $
        validateAuxiliaryData @era md' ?! embed InvalidMetadata

  -- check genesis keys signatures for instantaneous rewards certificates
  let genDelegates =
        Set.fromList $
          fmap (asWitness . genDelegKeyHash) $
            Map.elems genMapping
      (WitHashes khAsSet) = witsKeyHashes
      genSig = eval (genDelegates ∩ khAsSet)
      mirCerts =
        StrictSeq.forceToStrict
          . Seq.filter isInstantaneousRewards
          . StrictSeq.fromStrict
          $ getField @"certs" txbody
      GenDelegs genMapping = genDelegs

  coreNodeQuorum <- liftSTS $ asks quorum
  ( (not $ null mirCerts)
      ==> Set.size genSig >= fromIntegral coreNodeQuorum
    )
    ?! (embed (MIRInsufficientGenesisSigsUTXOW genSig))

  trans @(Core.EraRule "UTXO" era) $
    TRC (UtxoEnv slot pp stakepools genDelegs, u, tx)

instance
  ( Era era,
    STS (UTXO era),
    PredicateFailure (Core.EraRule "UTXO" era) ~ UtxoPredicateFailure era
  ) =>
  Embed (UTXO era) (UTXOW era)
  where
  wrapFailed = UtxoFailure

instance
  ( -- Fix Core.Tx to the Shelley Era
    Core.Tx era ~ Tx era,
    -- Allow UTXOW to call UTXO
    Embed (Core.EraRule "UTXO" era) (UTXOW era),
    Environment (Core.EraRule "UTXO" era) ~ UtxoEnv era,
    State (Core.EraRule "UTXO" era) ~ UTxOState era,
    Signal (Core.EraRule "UTXO" era) ~ Tx era,
    PredicateFailure (UTXOW era) ~ UtxowPredicateFailure era,
    -- Supply the HasField and Validate instances for Shelley
    ShelleyStyleWitnessNeeds era
  ) =>
  STS (UTXOW era)
  where
  type State (UTXOW era) = UTxOState era
  type Signal (UTXOW era) = Tx era
  type Environment (UTXOW era) = UtxoEnv era
  type BaseM (UTXOW era) = ShelleyBase
  type PredicateFailure (UTXOW era) = UtxowPredicateFailure era
  transitionRules = [shelleyStyleWitness id]
  initialRules = [initialLedgerStateUTXOW]
