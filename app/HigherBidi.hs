{-# LANGUAGE LambdaCase #-}
{-# OPTIONS_GHC -Wno-name-shadowing #-}
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

import Control.Monad.State.Strict (State, modify', get)
import Data.List (delete)
import Data.Maybe (mapMaybe)
import GHC.List (foldl')
import GHC.Stack (HasCallStack)


-----------------------------------------------------------------------
-- Expressions

-- | Source expressions: Figure 1.
data Expr
  = Var String       -- ^ Variable
  | Unit             -- ^ Unit
  | Lam String Expr  -- ^ Lambda
  | App Expr Expr    -- ^ Application
  | Ann Expr Type    -- ^ Annotated type
  deriving (Show)


-----------------------------------------------------------------------
-- Types

-- | An existential type variable.
newtype TypVar = TypVar Int
 deriving (Show, Eq)

-- | The type of a type: Figure 6.
data Type
  = TUnit                -- ^ 1
  | TVar TypVar          -- ^ α
  | TExt TypVar          -- ^ α̂
  | TForall TypVar Type  -- ^ ∀α. A
  | Type :-> Type        -- ^ A → B
 deriving (Show, Eq)
infixr :->

-- | A type without quantification: Figure 6.
data Monotype
  = MTUnit                 -- ^ 1
  | MTVar TypVar           -- ^ α
  | MTExt TypVar           -- ^ α̂
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

polyToMono :: Type -> Maybe Monotype
polyToMono = \case
  TUnit -> Just MTUnit
  TVar s -> Just $ MTVar s
  TExt α̂ -> Just $ MTExt α̂
  a :-> b -> do
    τ <- polyToMono a
    σ <- polyToMono b
    pure $ τ :-< σ
  TForall _ _ -> Nothing

-- | Free variables.
fv :: Type -> [TypVar]
fv = \case
  TUnit       -> []
  TVar α      -> [α]
  TExt α̂      -> [α̂]
  TForall α a -> delete α (fv a)
  a :-> b     -> fv a ++ fv b


-----------------------------------------------------------------------
-- Context

-- | What's in a context: Figure 6.
data CtxItem
  = CVar TypVar          -- ^ α
  | CAnn String Type     -- ^ x : A
  | CUns TypVar          -- ^ α̂
  | CSol TypVar Monotype -- ^ α̂ = τ
  | CMar TypVar          -- ^ ▸α̂
  deriving (Eq, Show)

-- | A context.
type Ctx = [CtxItem]

fresh :: State Int TypVar
fresh = do
  modify' (+ 1)
  TypVar <$> get

dropAfterItem :: CtxItem -> Ctx -> Ctx
dropAfterItem item = takeWhile (/= item)

-- | Split a context Γ into Γ',A,Γ''.
splitCtx :: Ctx -> CtxItem -> (Ctx, Ctx)
splitCtx ctx a = case r of
  []       -> (l, []) -- should be impossible, given a well-formed context
  (_ : r') -> (l, r')
 where
  (l, r) = break (== a) ctx

-- | `leftOf Γ α β` checks whether α occurs to the left of β in Γ.
leftOf :: Ctx -> CtxItem -> CtxItem -> Bool
leftOf ctx α β = go False ctx
 where
  go :: Bool -> [CtxItem] -> Bool
  go _     []       = die
  go αSeen (c : cs)
    | c == β    = αSeen
    | c == α    = go True cs
    | otherwise = go αSeen cs

-----------------------------------------------------------------------
-- Well-formedness

-- | Γ ⊢ A: Under context Γ, type A is well-formed. Figure 7.
wellFormed :: [CtxItem] -> Type -> Bool
wellFormed ctx = \case
  TUnit       -> True                                   -- UnitWF
  TVar α      -> CVar α `elem` ctx                           -- UvarWF
  TExt α̂      -> CUns α̂ `elem` ctx || isSolved α̂             -- EvarWF and SolvedEvarWF
  TForall s t -> wellFormed (ctx ++ [CVar s]) t         -- ForallWF
  t₁ :-> t₂   -> wellFormed ctx t₁ && wellFormed ctx t₂ -- ArrowWF
 where
  isSolved :: TypVar -> Bool
  isSolved α̂ = or [ α̂ == β̂ | CSol β̂ _ <- ctx ]

-- | Γ ctx: Algorithmic context Γ is well-formed. Figure 7.
wellFormedΓ :: [CtxItem] -> Bool
wellFormedΓ = \case
  []       -> True                                                             -- EmptyCtx
  (c : cs) -> case c of
    CVar α   -> wellFormedΓ cs && CVar α `notElem` cs                                  -- UvarCtx
    CAnn x t -> wellFormedΓ cs && x `notElem` domAnn cs && wellFormed cs t             -- VarCtx
    CUns α̂   -> wellFormedΓ cs && α̂ `notElem` domEx cs                                 -- EvarCtx
    CSol α̂ τ -> wellFormedΓ cs && α̂ `notElem` domEx cs && wellFormed cs (monoToPoly τ) -- SolvedEvarCtx
    CMar α̂   -> wellFormedΓ cs && CMar α̂ `notElem` cs && α̂ `notElem` domEx cs                  -- MarkerCtx
 where
  domAnn :: [CtxItem] -> [String]
  domAnn ctx = [ x | CAnn x _ <- ctx ]

  domEx :: [CtxItem] -> [TypVar]
  domEx = mapMaybe (\case CUns α̂   -> Just α̂
                          CSol α̂ _ -> Just α̂
                          _        -> Nothing)


-----------------------------------------------------------------------
-- Substitutions

-- | Apply a context, as a substitution, to a type: Figure 8.
applyCtx :: [CtxItem] -> Type -> Type
applyCtx ctx typ =
  foldl' (\accType -> \case
             CSol α̂ τ -> subst α̂ τ accType
             _        -> accType)
         typ
         ctx
 where
  subst :: TypVar -> Monotype -> Type -> Type
  subst α̂ τ = \case
    t@(TExt β̂)  -> if α̂ == β̂ then monoToPoly τ else t
    t₁ :-> t₂   -> subst α̂ τ t₁ :-> subst α̂ τ t₂
    TForall s t -> TForall s (subst α̂ τ t)
    t           -> t

-- | [B.α]A: substitute a type variable for another type in a type.
substType :: Type -> TypVar -> Type -> Type
substType to from = go
 where
  go :: Type -> Type
  go = \case
    TVar α      -> if α == from then to else TVar α
    TExt α̂      -> if α̂ == from then to else TExt α̂
    TForall α a -> TForall α (if α == from then a else go a)
    a :-> b     -> go a :-> go b
    TUnit       -> TUnit


-----------------------------------------------------------------------
-- Subtyping

-- | Γ ⊢ A <: B ⊣ Δ: Under input context Γ, type A is a subtype of B, with
-- output context Δ. Figure 9.
subtype :: Ctx -> Type -> Type -> State Int Ctx
subtype ctx a b
  | wellFormed ctx a && wellFormed ctx b = case (a, b) of
      (TVar α, TVar β)       -> if α == β then pure ctx else die  -- <:Var
      (TUnit, TUnit)         -> pure ctx                          -- <:Unit
      (TExt α̂, TExt β̂)       -> if α̂ == β̂ then pure ctx else die  -- <:Exvar
      (a₁ :-> a₂, b₁ :-> b₂) -> do                                -- <:→
        ctxΘ <- subtype ctx b₁ a₁
        let a₂Θ = applyCtx ctxΘ a₂                     -- [Θ]A₂
            b₂Θ = applyCtx ctxΘ b₂                     -- [Θ]B₂
        subtype ctxΘ a₂Θ b₂Θ
      (TForall α a, b) -> do                                      -- <:∀L
        freshα̂ <- fresh
        let extCtx = ctx ++ [CMar freshα̂, CUns freshα̂] -- Γ,▸α̂,α̂
            substA = substType (TExt freshα̂) α a       -- [α̂/α]A
        ctxΔ <- subtype extCtx substA b                -- Δ,▸α̂,Θ
        pure $ dropAfterItem (CMar freshα̂) ctxΔ        -- Δ
      (a, TForall α b) -> do                                      -- <:∀R
        freshα <- fresh
        let extendedCtx = ctx ++ [CUns freshα]         -- Γ,α
            -- N.b.: not in Figure 9, but important in the
            -- implementation! Otherwise, we might get
            -- name-clashes and drop the wrong things.
            cleanB = substType (TVar freshα) α b       -- B
        ctxΔ <- subtype extendedCtx a cleanB           -- Δ,α,Θ
        pure $ dropAfterItem (CUns freshα) ctxΔ        -- Δ
      (TExt α̂, a) -> do                                           -- <:InstantiateL
        if α̂ `notElem` fv a
          then instantiateL ctx α̂ a
          else die
      (a, TExt α̂) -> do                                           -- <:InstantiateR
        if α̂ `notElem` fv a
          then instantiateR ctx a α̂
          else die
      _ -> die
  | otherwise = die


-----------------------------------------------------------------------
-- Instantiation

-- | Γ ⊢ α̂ :=< A ⊣ Δ: Under input context Γ, instantiate α̂ such that α̂ <: A,
-- with output context Δ.
instantiateL :: Ctx -> TypVar -> Type -> State Int Ctx
instantiateL ctx α̂ a = case polyToMono a of
  Just τ -> do                                               -- InstLSolve
    let (ctxL, ctxR) = splitCtx ctx (CUns α̂)
    if wellFormed ctxL a
      then pure $ ctxL ++ [CSol α̂ τ] ++ ctxR
      else die
  Nothing -> case a of
    TExt β̂ -> if leftOf ctx (CUns α̂) (CUns β̂)                -- InstLReach
      then let (ctxL, ctxR) = splitCtx ctx (CUns β̂)
           in pure $ ctxL ++ [CSol β̂ (MTVar α̂)] ++ ctxR
      else let (ctxL, ctxR) = splitCtx ctx (CUns α̂)
           in pure $ ctxL ++ [CSol α̂ (MTVar β̂)] ++ ctxR
    a₁ :-> a₂ -> do                                          -- InstLArr
      let (ctxL, ctxR) = splitCtx ctx (CUns α̂)
      â₁ <- fresh
      â₂ <- fresh
      let extCtx = mconcat
            [ ctxL
            , [ CUns â₂
              , CUns â₁
              , CSol α̂ (MTVar â₁ :-< MTVar â₂)
              ]
            , ctxR
            ]
      ctxΘ <- instantiateR extCtx a₁ â₁
      instantiateL ctxΘ â₂ (applyCtx ctxΘ a₂)
    TForall β b -> do                                        -- InstLAIIR
      β̂fresh <- fresh
      let extCtx = ctx ++ [CMar β̂fresh, CUns β̂fresh]
          substB = substType (TExt β̂fresh) β b
      ctxΔ <- instantiateL extCtx α̂ substB
      pure $ dropAfterItem (CMar β̂fresh) ctxΔ
    _ -> die

-- | Γ ⊢ A =:< α̂ ⊣ Δ: Under input context Γ, instantiate α̂ such that A <: α̂,
-- with output context Δ.
instantiateR :: Ctx -> Type -> TypVar -> State Int Ctx
instantiateR ctx a α̂ = case polyToMono a of
  Just _  -> instantiateL ctx α̂ a                            -- InstRSolve
  Nothing -> case a of
    TExt _ -> instantiateL ctx α̂ a                           -- InstRReach
    a₁ :-> a₂ -> do                                          -- InstRArr
      let (ctxL, ctxR) = splitCtx ctx (CUns α̂)
      â₁ <- fresh
      â₂ <- fresh
      let extCtx = mconcat
            [ ctxL
            , [ CUns â₂
              , CUns â₁
              , CSol α̂ (MTVar â₁ :-< MTVar â₂)
              ]
            , ctxR
            ]
      ctxΘ <- instantiateL extCtx â₁ a₁
      instantiateR ctxΘ (applyCtx ctxΘ a₂) â₂
    TForall β b -> do                                        -- InstRAIIL
      βfresh <- fresh
      let extCtx = ctx ++ [CUns βfresh]
          cleanB = substType (TVar βfresh) β b
      ctxΔ <- instantiateL extCtx α̂ cleanB
      pure $ dropAfterItem (CVar βfresh) ctxΔ
    _ -> die

-----------------------------------------------------------------------
-- Util

-- | Any use of 'die' is a possibility for good error reporting!
die :: HasCallStack => a
die = error "error"
