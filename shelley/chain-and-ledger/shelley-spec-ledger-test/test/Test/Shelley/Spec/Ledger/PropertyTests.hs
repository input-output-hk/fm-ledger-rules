{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DoAndIfThenElse #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}

module Test.Shelley.Spec.Ledger.PropertyTests
  ( propertyTests,
    minimalPropertyTests,
  )
where

import Cardano.Binary (ToCBOR)
import qualified Cardano.Ledger.Core as Core
import Cardano.Ledger.Era (Crypto)
import Cardano.Ledger.Shelley.Constraints (TransValue)
import Control.State.Transition
import qualified Control.State.Transition.Trace.Generator.QuickCheck as QC
import Data.Sequence (Seq)
import Data.Sequence.Strict (StrictSeq)
import Data.Set (Set)
import GHC.Records (HasField (..))
import Shelley.Spec.Ledger.API (CHAIN, DPState, DelegsEnv, Tx, UTxOState, UtxoEnv)
import Shelley.Spec.Ledger.BaseTypes
  ( StrictMaybe (..),
  )
import Shelley.Spec.Ledger.Delegation.Certificates (DCert)
import Shelley.Spec.Ledger.PParams (Update (..))
import Shelley.Spec.Ledger.STS.Ledger (LEDGER)
import Shelley.Spec.Ledger.TxBody (TxIn, Wdrl)
import Test.Shelley.Spec.Ledger.Address.Bootstrap
  ( bootstrapHashTest,
  )
import Test.Shelley.Spec.Ledger.Address.CompactAddr
  ( propCompactAddrRoundTrip,
    propCompactSerializationAgree,
    propDecompactAddrLazy,
    propDecompactShelleyLazyAddr,
  )
import Test.Shelley.Spec.Ledger.ByronTranslation (testGroupByronTranslation)
import Test.Shelley.Spec.Ledger.Generator.Core (GenEnv)
import Test.Shelley.Spec.Ledger.Generator.EraGen (EraGen)
import Test.Shelley.Spec.Ledger.Rules.ClassifyTraces
  ( onlyValidChainSignalsAreGenerated,
    onlyValidLedgerSignalsAreGenerated,
    relevantCasesAreCovered,
  )
import Test.Shelley.Spec.Ledger.Rules.TestChain
  ( adaPreservationChain,
    collisionFreeComplete,
    delegProperties,
    poolProperties,
    removedAfterPoolreap,
  )
import Test.Shelley.Spec.Ledger.ShelleyTranslation (testGroupShelleyTranslation)
import Test.Shelley.Spec.Ledger.Utils (ChainProperty, ShelleyTest)
import Test.Tasty (TestTree, testGroup)
import qualified Test.Tasty.QuickCheck as TQC

minimalPropertyTests ::
  forall era.
  ( EraGen era,
    ShelleyTest era,
    TransValue ToCBOR era,
    ChainProperty era,
    QC.HasTrace (CHAIN era) (GenEnv era),
    Embed (Core.EraRule "DELEGS" era) (LEDGER era),
    Environment (Core.EraRule "DELEGS" era) ~ DelegsEnv era,
    State (Core.EraRule "DELEGS" era) ~ DPState (Crypto era),
    Signal (Core.EraRule "DELEGS" era) ~ Seq (DCert (Crypto era)),
    Embed (Core.EraRule "UTXOW" era) (LEDGER era),
    Environment (Core.EraRule "UTXOW" era) ~ UtxoEnv era,
    State (Core.EraRule "UTXOW" era) ~ UTxOState era,
    Signal (Core.EraRule "UTXOW" era) ~ Tx era,
    HasField "inputs" (Core.TxBody era) (Set (TxIn (Crypto era))),
    HasField "certs" (Core.TxBody era) (StrictSeq (DCert (Crypto era))),
    HasField "wdrls" (Core.TxBody era) (Wdrl (Crypto era)),
    HasField "update" (Core.TxBody era) (StrictMaybe (Update era)),
    Show (State (Core.EraRule "PPUP" era))
  ) =>
  TestTree
minimalPropertyTests =
  testGroup
    "Minimal Property Tests"
    [ TQC.testProperty "Chain and Ledger traces cover the relevant cases" (relevantCasesAreCovered @era),
      TQC.testProperty "total amount of Ada is preserved (Chain)" (adaPreservationChain @era),
      TQC.testProperty "Only valid CHAIN STS signals are generated" (onlyValidChainSignalsAreGenerated @era),
      bootstrapHashTest,
      testGroup
        "Compact Address Tests"
        [ TQC.testProperty "Compact address round trip" (propCompactAddrRoundTrip @(Crypto era)),
          TQC.testProperty "Compact address binary representation" (propCompactSerializationAgree @(Crypto era)),
          TQC.testProperty "determining address type doesn't force contents" (propDecompactAddrLazy @(Crypto era)),
          TQC.testProperty "reading the keyhash doesn't force the stake reference" (propDecompactShelleyLazyAddr @(Crypto era))
        ]
    ]

-- | 'TestTree' of property-based testing properties.
propertyTests ::
  forall era.
  ( EraGen era,
    ShelleyTest era,
    TransValue ToCBOR era,
    ChainProperty era,
    QC.HasTrace (CHAIN era) (GenEnv era),
    QC.HasTrace (LEDGER era) (GenEnv era),
    Embed (Core.EraRule "DELEGS" era) (LEDGER era),
    Environment (Core.EraRule "DELEGS" era) ~ DelegsEnv era,
    State (Core.EraRule "DELEGS" era) ~ DPState (Crypto era),
    Signal (Core.EraRule "DELEGS" era) ~ Seq (DCert (Crypto era)),
    Embed (Core.EraRule "UTXOW" era) (LEDGER era),
    Environment (Core.EraRule "UTXOW" era) ~ UtxoEnv era,
    State (Core.EraRule "UTXOW" era) ~ UTxOState era,
    Signal (Core.EraRule "UTXOW" era) ~ Tx era,
    HasField "inputs" (Core.TxBody era) (Set (TxIn (Crypto era))),
    HasField "certs" (Core.TxBody era) (StrictSeq (DCert (Crypto era))),
    HasField "wdrls" (Core.TxBody era) (Wdrl (Crypto era)),
    HasField "update" (Core.TxBody era) (StrictMaybe (Update era)),
    Show (State (Core.EraRule "PPUP" era))
  ) =>
  TestTree
propertyTests =
  testGroup
    "Property-Based Testing"
    [ testGroup
        "Classify Traces"
        [ TQC.testProperty
            "Chain and Ledger traces cover the relevant cases"
            (relevantCasesAreCovered @era)
        ],
      testGroup
        "STS Rules - Delegation Properties"
        [ TQC.testProperty
            "properties of the DELEG STS"
            (delegProperties @era)
        ],
      testGroup
        "STS Rules - Pool Properties"
        [ TQC.testProperty
            "properties of the POOL STS"
            (poolProperties @era)
        ],
      testGroup
        "STS Rules - Poolreap Properties"
        [ TQC.testProperty
            "pool is removed from stake pool and retiring maps"
            (removedAfterPoolreap @era)
        ],
      testGroup
        "CHAIN level Properties"
        [ TQC.testProperty
            "collection of Ada preservation properties"
            (adaPreservationChain @era),
          TQC.testProperty
            "inputs are eliminated, outputs added to utxo and TxIds are unique"
            (collisionFreeComplete @era)
        ],
      testGroup
        "Properties of Trace generators"
        [ TQC.testProperty
            "Only valid LEDGER STS signals are generated"
            (onlyValidLedgerSignalsAreGenerated @era),
          TQC.testProperty
            "Only valid CHAIN STS signals are generated"
            (onlyValidChainSignalsAreGenerated @era)
        ],
      testGroupByronTranslation,
      testGroupShelleyTranslation,
      testGroup
        "Compact Address Tests"
        [ TQC.testProperty "Compact address round trip" (propCompactAddrRoundTrip @(Crypto era)),
          TQC.testProperty "Compact address binary representation" (propCompactSerializationAgree @(Crypto era)),
          TQC.testProperty "determining address type doesn't force contents" (propDecompactAddrLazy @(Crypto era)),
          TQC.testProperty "reading the keyhash doesn't force the stake reference" (propDecompactShelleyLazyAddr @(Crypto era))
        ]
    ]
