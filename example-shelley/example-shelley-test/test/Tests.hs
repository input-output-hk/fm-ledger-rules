{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TypeApplications #-}

module Main where

import Cardano.Ledger.Example (ExampleEra)
import Test.Cardano.Ledger.Example ()
import Test.Shelley.Spec.Ledger.ConcreteCryptoTypes (C_Crypto)
import Test.Shelley.Spec.Ledger.PropertyTests (minimalPropertyTests, propertyTests)
import Test.Tasty
import Test.Tasty.HUnit ()
import Test.TestScenario (TestScenario (..), mainWithTestScenario)

tests :: TestTree
tests = askOption $ \case
  Nightly -> nightlyTests
  Fast -> mainTests
  _ -> mainTests

mainTests :: TestTree
mainTests =
  testGroup
    "Example Consensus Tests"
    [ minimalPropertyTests @(ExampleEra C_Crypto)
    ]

nightlyTests :: TestTree
nightlyTests =
  testGroup
    "Example Consensus - nightly"
    [ testGroup
        "Example Era - nightly"
        [ propertyTests @(ExampleEra C_Crypto)
        ]
    ]

-- main entry point
main :: IO ()
main = mainWithTestScenario tests
