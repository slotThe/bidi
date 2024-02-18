{-# LANGUAGE LambdaCase #-}
{- |
   Module      : Bidi
   Description : Bidirectional type inference for the simply typed lambda calculus
   Copyright   : (c) Tony Zorman, 2024
   License     : GPL-3
   Maintainer  : Tony Zorman <soliditsallgood@mailbox.org>

A very basic bidirectional type-checking algorithm for a very basic simply
typed lambda calculus. The main source was the following survey:

  - Jana Dunfield and Neel Krishnaswami. 2021. Bidirectional Typing. ACM Comput. Surv. 54, 5, Article 98 (June 2022), 38 pages. https://doi.org/10.1145/3450952

The article is readily available <https://arxiv.org/abs/1908.05839 on the arXiv>.
-}
module Bidi where

import qualified Data.Map.Strict as Map
import Data.Map (Map)

data Expr
  = Var String       -- ^ Variable
  | Ann Expr Type    -- ^ Annotated type
  | Lam String Expr  -- ^ Lambda
  | App Expr Expr    -- ^ Application
  | Unit             -- ^ Unit
  deriving (Show)

data Type = TUnit | Type :-> Type
 deriving (Show, Eq)
infixr :->

type Ctx = Map String Type

eConst :: Expr
eConst = Lam "x" (Lam "y" (Var "x"))

tId :: Type
tId = TUnit :-> TUnit
eId :: Expr
eId = Lam "x" (Var "x")

infer :: Ctx -> Expr -> Type
infer ctx = \case
  Var x -> case ctx Map.!? x of
    Just t  -> t
    Nothing -> error $ "Variable not in scope: " <> show x
  Ann e t ->
    if t == t' then t
    else error $ "Wrong annotation: " <> show e <> " has annotation "
              <> show t <> " while it's actual time is " <> show t'
   where t' = check ctx t e
  App e₁ e₂ -> case infer ctx e₁ of
    t :-> t' -> if t == t₂ then t'
                else error $ "Can't match types in application: parameter has type "
                          <> show t <> " but argument has type " <> show t₂
     where t₂ = check ctx t e₂
    _ -> error $ "Can't apply " <> show e₂ <> " to non-function " <> show e₁
  e -> error $ "Can't infer type of " <> show e

check :: Ctx -> Type -> Expr -> Type
check _   TUnit       Unit      = TUnit
check ctx (t₁ :-> t₂) (Lam x e) = t₁ :-> check (Map.insert x t₁ ctx) t₂ e
-- Have some semblance of type inference by not having to annotate every
-- single term
check ctx t e
  | t == t'   = t
  | otherwise = error $ "check: Expected " <> show t <> " but got " <> show t'
                     <> " in expression " <> show e
 where t' = infer ctx e
