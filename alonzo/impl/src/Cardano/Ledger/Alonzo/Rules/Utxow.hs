{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}

module Cardano.Ledger.Alonzo.Rules.Utxow where

-- import Cardano.Ledger.SafeHash (HashAnnotated)

import Cardano.Ledger.AuxiliaryData
  ( ValidateAuxiliaryData (..),
    hashAuxiliaryData,
  )
import qualified Cardano.Ledger.Core as Core
import Cardano.Ledger.Era (Crypto, Era)
import Control.Iterate.SetAlgebra (eval, (∩))
import Control.Monad (when)
import Control.Monad.Trans.Reader (asks)
import Control.State.Transition.Extended
import qualified Data.Map.Strict as Map
import qualified Data.Sequence as Seq (filter)
import Data.Sequence.Strict (StrictSeq)
import qualified Data.Sequence.Strict as StrictSeq
import Data.Set (Set)
import qualified Data.Set as Set
import GHC.Records
import Shelley.Spec.Ledger.BaseTypes
  ( ShelleyBase,
    StrictMaybe (..),
    quorum,
    (==>),
  )
import Shelley.Spec.Ledger.Delegation.Certificates (isInstantaneousRewards)
import Shelley.Spec.Ledger.Keys (DSignable, GenDelegs (..), Hash, KeyRole (Witness), asWitness, genDelegKeyHash)
import Shelley.Spec.Ledger.LedgerState
  ( UTxOState (..),
    WitHashes (..),
    diffWitHashes,
    nullWitHashes,
    verifiedWits,
    witsFromTxWitnesses,
    witsVKeyNeeded,
  )
import Shelley.Spec.Ledger.PParams (ProtVer, Update (..))
import Shelley.Spec.Ledger.STS.Utxo (UtxoEnv (..))
import Shelley.Spec.Ledger.STS.Utxow (UtxowPredicateFailure (..))
import qualified Shelley.Spec.Ledger.SoftForks as SoftForks
import Shelley.Spec.Ledger.Tx (TxIn, ValidateScript (..), WitVKey)
import Shelley.Spec.Ledger.TxBody
  ( DCert,
    EraIndependentTxBody,
    Wdrl,
  )
import Shelley.Spec.Ledger.UTxO (scriptsNeeded)

-- =====================================================

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

-- ====================================

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
    PredicateFailure (utxow era) ~ UtxowPredicateFailure era,
    STS (utxow era),
    ShelleyStyleWitnessNeeds era
  ) =>
  TransitionRule (utxow era)
shelleyStyleWitness = do
  (TRC (UtxoEnv slot pp stakepools genDelegs, u, tx)) <- judgmentContext
  let txbody = getField @"body" tx
      auxdata = getField @"auxiliaryData" tx
      utxo = _utxo u
      witsKeyHashes = witsFromTxWitnesses @era tx

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
    fs -> failBecause $ ScriptWitnessNotValidatingUTXOW $ Set.fromList $ fmap fst fs

  let sNeeded = scriptsNeeded utxo tx
      sReceived = Map.keysSet (getField @"scriptWits" tx)
  sNeeded == sReceived
    ?! MissingScriptWitnessesUTXOW
      (sNeeded `Set.difference` sReceived)

  -- check VKey witnesses
  verifiedWits @era tx ?!: InvalidWitnessesUTXOW

  let needed = witsVKeyNeeded @era utxo tx genDelegs
      missingWitnesses = diffWitHashes needed witsKeyHashes
      haveNeededWitnesses = case nullWitHashes missingWitnesses of
        True -> Right ()
        False -> Left missingWitnesses
  haveNeededWitnesses ?!: MissingVKeyWitnessesUTXOW

  -- check metadata hash
  case (getField @"adHash" txbody, auxdata) of
    (SNothing, SNothing) -> pure ()
    (SJust mdh, SNothing) -> failBecause $ MissingTxMetadata mdh
    (SNothing, SJust md') ->
      failBecause $
        MissingTxBodyMetadataHash (hashAuxiliaryData @era md')
    (SJust mdh, SJust md') -> do
      hashAuxiliaryData @era md' == mdh
        ?! ConflictingMetadataHash mdh (hashAuxiliaryData @era md')
      -- check metadata value sizes
      when (SoftForks.validMetadata pp) $
        validateAuxiliaryData @era md' ?! InvalidMetadata

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
    ?! MIRInsufficientGenesisSigsUTXOW genSig

  trans @(Core.EraRule "UTXO" era) $
    TRC (UtxoEnv slot pp stakepools genDelegs, u, tx)
