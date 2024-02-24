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

NOTE: Alignment of comments might be missing off due to some personal
`prettify-symbols-mode` settings for `haskell-mode`. Sorry.
-}
module HigherBidi where

import GHC.List (foldl')
import Data.Maybe (mapMaybe)

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
monoToPoly :: Monotype -> Type
monoToPoly = \case
  MTUnit -> TUnit
  MTVar s -> TVar s
  MTExt α̂ -> TExt α̂
  τ :-< σ -> monoToPoly τ :-> monoToPoly σ

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
  isSolved α̂ = or [ α̂ == β̂ | CSol β̂ _ <- ctx ]

-- | Γ ctx: Algorithmic context Γ is well-formed. Figure 7.
wellFormedΓ :: Ctx -> Bool
wellFormedΓ = \case
  []       -> True                                                             -- EmptyCtx
  (c : cs) -> case c of
    CVar α   -> wellFormedΓ cs && CVar α `notElem` cs                                  -- UvarCtx
    CAnn x t -> wellFormedΓ cs && x `notElem` domAnn cs && wellFormed cs t             -- VarCtx
    CUns α̂   -> wellFormedΓ cs && α̂ `notElem` domEx cs                                 -- EvarCtx
    CSol α̂ τ -> wellFormedΓ cs && α̂ `notElem` domEx cs && wellFormed cs (monoToPoly τ) -- SolvedEvarCtx
    CMar α̂   -> wellFormedΓ cs && CMar α̂ `notElem` cs && α̂ `notElem` domEx cs                  -- MarkerCtx
 where
  domAnn :: Ctx -> [String]
  domAnn ctx = [ x | CAnn x _ <- ctx ]

  domEx :: Ctx -> [Existential]
  domEx = mapMaybe (\case CUns α̂   -> Just α̂
                          CSol α̂ _ -> Just α̂
                          _        -> Nothing)

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
    t@(TExt β̂)  -> if α̂ == β̂ then monoToPoly τ else t
    t₁ :-> t₂   -> subst α̂ τ t₁ :-> subst α̂ τ t₂
    TForall s t -> TForall s (subst α̂ τ t)
    t           -> t
