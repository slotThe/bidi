{-# LANGUAGE LambdaCase #-}
{- |
   Module      : HigherBidi
   Description : Complete and Easy Bidirectional Typechecking for Higher-Rank Polymorphism
   Copyright   : (c) Tony Zorman, 2024
   License     : GPL-3
   Maintainer  : Tony Zorman <soliditsallgood@mailbox.org>
   Stability   : experimental
   Portability : non-portable

A bidirectional typechecking algorithm for a very basic simply
typed lambda calculus. The main source was the following survey:

  - Jana Dunfield and Neelakantan R. Krishnaswami. 2013. Complete and easy bidirectional typechecking for higher-rank polymorphism. In Proceedings of the 18th ACM SIGPLAN international conference on Functional programming (ICFP '13). Association for Computing Machinery, New York, NY, USA, 429–442. https://doi.org/10.1145/2500365.2500582

The article is readily available <https://arxiv.org/abs/1306.6032 on the arXiv>.
-}
module HigherBidi where

import GHC.List (foldl')

-- | Source expressions: Figure 1.
data Expr
  = Var String       -- ^ Variable
  | Unit             -- ^ Unit
  | Lam String Expr  -- ^ Lambda
  | App Expr Expr    -- ^ Application
  | Ann Expr Type    -- ^ Annotated type
  deriving (Show)

-- | An existential type variable.
newtype Existential = Ex Int
 deriving (Show, Eq)

-- | The type of a type: Figure 6.
data Type
  = TUnit                -- ^ 1
  | TVar String          -- ^ α
  | TExt Existential     -- ^ α̂
  | TForall String Type  -- ^ ∀α. A
  | Type :-> Type        -- ^ A → B
 deriving (Show, Eq)
infixr :->

-- | A type without quantification: Figure 6.
data Monotype
  = MTUnit                 -- ^ 1
  | MTVar String           -- ^ α
  | MTExt Existential      -- ^ α̂
  | Monotype :-< Monotype  -- ^ τ → σ
 deriving (Show, Eq)
infixr :-<

-- | Turn a 'Monotype' into a real 'Type'.
monoToType :: Monotype -> Type
monoToType = \case
  MTUnit -> TUnit
  MTVar s -> TVar s
  MTExt α̂ -> TExt α̂
  τ :-< σ -> monoToType τ :-> monoToType σ

-- | What's in a context: Figure 6.
data CtxItem
  = CVar String               -- ^ α
  | CAnn String Type          -- ^ x : A
  | CUns Existential          -- ^ α̂
  | CSol Existential Monotype -- ^ α̂ = τ
  | CMar Existential          -- ^ ▸α̂
  deriving (Eq, Show)

-- | A context.
type Ctx = [CtxItem]

-- | Apply a context, as a substitution, to a type: Figure 8.
applyCtx :: Ctx -> Type -> Type
applyCtx ctx typ =
  foldl' (\accType -> \case
             CSol α̂ τ -> subst α̂ τ accType
             _        -> accType)
         typ
         ctx
 where
  subst :: Existential -> Monotype -> Type -> Type
  subst α̂ τ = \case
    t@(TExt β̂)  -> if α̂ == β̂ then monoToType τ else t
    t₁ :-> t₂   -> subst α̂ τ t₁ :-> subst α̂ τ t₂
    TForall s t -> TForall s (subst α̂ τ t)
    t           -> t

-- | Γ ⊢ A: Under context Γ, type A is well-formed. Figure 7.
wellFormed :: Ctx -> Type -> Bool
wellFormed ctx = \case
  TUnit       -> True                                   -- UnitWF
  TVar α      -> CVar α `elem` ctx                           -- UvarWF
  TExt α̂      -> CUns α̂ `elem` ctx || isSolved α̂             -- EvarWF and SolvedEvarWF
  TForall s t -> wellFormed (CVar s : ctx) t            -- ForallWF
  t₁ :-> t₂   -> wellFormed ctx t₁ && wellFormed ctx t₂ -- ArrowWF
 where
  isSolved :: Existential -> Bool
  isSolved α̂ = any (\case CSol β̂ _ -> α̂ == β̂; _ -> False) ctx