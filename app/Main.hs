module Main where

import Bidi
import GHC.Exts
import Data.Foldable (traverse_)

main :: IO ()
main = traverse_ (print . uncurry infer)
  [ ( fromList [("x", TUnit)]
    , Ann eId tId
    )
  , ( fromList [("x", TUnit)]
    , Ann eConst (TUnit :-> TUnit :-> TUnit)
    )
  , ( fromList [("x", TUnit)]
    , App (Ann eId tId) Unit
    )
  , ( fromList [("x", TUnit), ("y", TUnit)]
    , App (App (Ann eConst ((TUnit :-> TUnit) :-> TUnit :-> TUnit :-> TUnit))
               eId)
          (Var "y")
    )
  ]
