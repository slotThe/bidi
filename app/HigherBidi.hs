{-# LANGUAGE BlockArguments #-}
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
module HigherBidi (
  typeCheck,
  test,
) where

import Control.Monad.State.Strict (State, evalState, get, modify')
import Data.List (delete, find)
import Data.Maybe (mapMaybe)
import GHC.Stack (HasCallStack)

test :: IO ()
test = do
  print $ typeCheck identity
  print $ typeCheck identity2
  print $ typeCheck (Ann identity2 (TForall tv (ttv :-> ttv)))
  print $ typeCheck (App identity Unit)
  print $ typeCheck (App (Lam "x" (Var "x")) Unit)
  print $ typeCheck (App (Lam "f" (App (Var "f") Unit)) identity)
  print $ typeCheck (Lam "x" (Lam "y" (Var "x")))
  print $ typeCheck (Lam "x" (Lam "x" (Var "x")))
  print $ typeCheck (Lam "x" (Lam "y" (Var "y")))
 where
  tv = TypVar (-1)
  ttv = TVar tv

  identity :: Expr
  identity = Ann (Lam "x" (Var "x")) (TForall tv (ttv :-> ttv))

  identity2 :: Expr
  identity2 = App identity identity

-- | Type check an expression.
typeCheck :: Expr -> (Type, Ctx)
typeCheck e = (applyCtx ctx typ, ctx)
 where
  (typ, ctx) = evalState (infer [] e) 0


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

-- | [e/x]f: Substitute the expression e for the variable x in the expression f.
substExpr :: Expr -> String -> Expr -> Expr
substExpr to from = go
 where
  go :: Expr -> Expr
  go = \case
    Var x     -> if x == from then to else Var x
    Unit      -> Unit
    App e₁ e₂ -> App (go e₁) (go e₂)
    Ann e a   -> Ann (go e) a
    Lam x e   -> Lam x (if x == from then e else go e)


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
  TUnit  -> Just MTUnit
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
  []       -> die     -- should be impossible, given a well-formed context
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

-- | Apply a context, as a substitution, to a type: Figure 8.
applyCtx :: [CtxItem] -> Type -> Type
applyCtx ctx typ =
  foldr (\c accType -> case c of
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
-- Subtyping

-- | Γ ⊢ A <: B ⊣ Δ: Under input context Γ, type A is a subtype of B, with
-- output context Δ. Figure 9.
subtype :: Ctx -> Type -> Type -> State Int Ctx
-- subtype ctx a b | trace ("subtype; ctx: " <> show ctx <> "  a: " <> show a <> "  b: " <> show b) False = undefined
subtype ctx a b = case (a, b) of
  (TVar α, TVar β)       ->                                           -- <:Var
    if α == β && wellFormed ctx a then pure ctx else die
  (TUnit, TUnit)         -> pure ctx                                  -- <:Unit
  (a₁ :-> a₂, b₁ :-> b₂) -> do                                        -- <:→
    ctxΘ <- subtype ctx b₁ a₁  -- Γ ⊢ B₁ <: A₁ ⊣ Θ
    subtype ctxΘ
            (applyCtx ctxΘ a₂) -- [Θ]A₂
            (applyCtx ctxΘ b₂) -- [Θ]B₂
  (a, TForall α b) -> do                                              -- <:∀R
    freshα <- fresh
    let extendedCtx = ctx ++ [CVar freshα]   -- Γ,α
        -- N.b.: not in Figure 9, but important in the
        -- implementation! Otherwise, we might get
        -- name-clashes and drop the wrong things.
        cleanB = substType (TVar freshα) α b -- B
    dropAfterItem (CVar freshα) <$>
      subtype extendedCtx a cleanB           -- Δ,α,Θ  →  Δ

  (TForall α a, b) -> do                                              -- <:∀L
    freshα̂ <- fresh
    let extCtx = ctx ++ [CMar freshα̂, CUns freshα̂] -- Γ,▸α̂,α̂
        substA = substType (TExt freshα̂) α a       -- [α̂/α]A
    dropAfterItem (CMar freshα̂) <$>
      subtype extCtx substA b                      -- Δ,▸α̂,Θ  →  Δ
  (TExt α̂, TExt β̂) | α̂ == β̂   -> pure ctx                             -- <:Exvar
  (TExt α̂, a)      | α̂ `notElem` fv a -> instantiateL ctx α̂ a                 -- <:InstantiateL
  (a, TExt α̂)      | α̂ `notElem` fv a -> instantiateR ctx a α̂                 -- <:InstantiateR
  _ -> die


-----------------------------------------------------------------------
-- Instantiation

-- | Γ ⊢ α̂ :=< A ⊣ Δ: Under input context Γ, instantiate α̂ such that α̂ <: A,
-- with output context Δ.
instantiateL :: Ctx -> TypVar -> Type -> State Int Ctx
-- instantiateL ctx α̂ a | trace ("instantiateL; ctx: " <> show ctx <> "  α̂: " <> show α̂ <> "  a: " <> show a) False = undefined
instantiateL ctx α̂ a = case instLSolve ctx α̂ a of
  Just ctx -> pure ctx                                             -- InstLSolve
  Nothing  -> case a of
    TExt β̂ | leftOf ctx (CUns α̂) (CUns β̂) ->                       -- InstLReach
      let (ctxL, ctxR) = splitCtx ctx (CUns β̂)
       in pure $ ctxL ++ [CSol β̂ (MTExt α̂)] ++ ctxR -- Γ[α̂][β̂ = α̂]
    a₁ :-> a₂ -> do                                                -- InstLArr
      α̂₁ <- fresh
      α̂₂ <- fresh
      let (ctxL, ctxR) = splitCtx ctx (CUns α̂)
          extCtx = mconcat   -- Γ[α̂₂,α̂₁,α̂ = α̂₁ → α̂₂]
            [ ctxL
            , [ CUns α̂₂
              , CUns α̂₁
              , CSol α̂ (MTExt α̂₁ :-< MTExt α̂₂)
              ]
            , ctxR
            ]
      ctxΘ <- instantiateR extCtx a₁ α̂₁
      instantiateL ctxΘ α̂₂ (applyCtx ctxΘ a₂)
    TForall β b -> do                                              -- InstLAIIR
      βfresh <- fresh
      let extCtx = ctx ++ [CVar βfresh]
          substB = substType (TVar βfresh) β b
      dropAfterItem (CVar βfresh) <$>
        instantiateL extCtx α̂ substB
    _ -> die

instLSolve :: Ctx -> TypVar -> Type -> Maybe Ctx
instLSolve ctx α̂ a = case polyToMono a of
  Just τ | wellFormed ctxL a -> Just $ ctxL ++ [CSol α̂ τ] ++ ctxR
  _                          -> Nothing
 where
  (ctxL, ctxR) = splitCtx ctx (CUns α̂)

-- | Γ ⊢ A =:< α̂ ⊣ Δ: Under input context Γ, instantiate α̂ such that A <: α̂,
-- with output context Δ.
instantiateR :: Ctx -> Type -> TypVar -> State Int Ctx
-- instantiateR ctx a α̂ | trace ("instantiateR; ctx: " <> show ctx <> "  a: " <> show a <> "  α̂: " <> show α̂) False = undefined
instantiateR ctx a α̂ = case instLSolve {- not a mistake! -} ctx α̂ a of
  Just ctx -> pure ctx                                       -- InstRSolve ≡ flip InstLSolve
  Nothing  -> case a of
    TExt{} -> instantiateL ctx α̂ a                           -- InstRReach ≡ flip InstLReach
    a₁ :-> a₂ -> do                                          -- InstRArr
      let (ctxL, ctxR) = splitCtx ctx (CUns α̂)
      â₁ <- fresh
      â₂ <- fresh
      let extCtx = mconcat -- Γ[α̂₂,α̂₁,α̂ = α̂₁ → α̂₂]
            [ ctxL
            , [ CUns â₂
              , CUns â₁
              , CSol α̂ (MTExt â₁ :-< MTExt â₂)
              ]
            , ctxR
            ]
      ctxΘ <- instantiateL extCtx â₁ a₁
      instantiateR ctxΘ (applyCtx ctxΘ a₂) â₂
    TForall β b -> do                                        -- InstRAIIL
      β̂fresh <- fresh
      let extCtx = ctx ++ [CMar β̂fresh, CUns β̂fresh]
          cleanB = substType (TExt β̂fresh) β b
      dropAfterItem (CMar β̂fresh) <$>
        instantiateR extCtx cleanB α̂
    _ -> die


-----------------------------------------------------------------------
-- Typing

-- | Γ ⊢ e ⇒ A ⊣ Δ: Under input context Γ, e synthesizes (infers) output type
-- A, with output context Δ.
infer :: Ctx -> Expr -> State Int (Type, Ctx)
-- infer ctx e | trace ("infer; ctx: " <> show ctx <> "  e: " <> show e) False = undefined
infer ctx e = case e of
  Var x   ->                                                      -- Var
    case find ((== x) . fst) [ (y, a) | CAnn y a <- ctx ] of -- (x : A) ∈ Γ
      Just (_, a) -> pure (a, ctx)
      Nothing     -> die
  Ann e a ->                                                      -- Anno
    if wellFormed ctx a
    then (a, ) <$> check ctx e a
    else die
  Unit    -> pure (TUnit, ctx)                                    -- 1l⇒
  Lam x e -> do                                                   -- →I⇒
    TypVar freshX <- fresh
    let x' = "_" <> show freshX -- psychological
    α̂ <- fresh
    β̂ <- fresh
    let extCtx = ctx ++ [ CUns α̂, CUns β̂, CAnn x' (TExt α̂) ]
        cleanE = substExpr (Var x') x e
    ctxΔ <- dropAfterItem (CAnn x' (TExt α̂)) <$> -- Δ
      check extCtx cleanE (TExt β̂)               -- Δ,x:α̂,Θ
    pure (TExt α̂ :-> TExt β̂, ctxΔ)
  App e₁ e₂ -> do                                                 -- →E
    (a, ctxΘ) <- infer ctx e₁
    appType ctxΘ (applyCtx ctxΘ a) e₂

-- | Γ ⊢ A ⇐ A ⊣ Δ: Under input context Γ, e checks against input type A, with
-- output context Δ.
check :: Ctx -> Expr -> Type -> State Int Ctx
-- check ctx e b | trace ("check; ctx" <> show ctx <> "  e: " <> show e <> "  b: " <> show b) False = undefined
check ctx e b = case (e, b) of
  (Unit, TUnit)    -> pure ctx                                    -- 1I
  (_, TForall α a) -> do                                          -- ∀I
    αfresh <- fresh
    let extCtx = ctx ++ [CVar αfresh]
        cleanA = substType (TVar αfresh) α a
    dropAfterItem (CVar αfresh) <$>
      check extCtx e cleanA
  (Lam x e, a :-> b) -> do                                        -- →I
    TypVar freshX <- fresh
    let x' = "_" <> show freshX -- psychological
    dropAfterItem (CAnn x' a) <$>     -- Δ
      check (ctx ++ [CAnn x' a])      -- Δ,x:A,Θ
            (substExpr (Var x') x e)
            b
  _ -> do                                                         -- Sub
    (a, ctxΘ) <- infer ctx e
    subtype ctxΘ (applyCtx ctxΘ a) (applyCtx ctxΘ b)

-- | Γ ⊢ A ∙ e ⇒> C ⊣ Δ: Under input context Γ, applying a function of type A
-- to e synthesises type C, with output context Δ.
appType :: Ctx -> Type -> Expr -> State Int (Type, Ctx)
-- appType ctx e b | trace ("appType; ctx" <> show ctx <> "  e: " <> show e <> "  b: " <> show b) False = undefined
appType ctx b e = case b of
  TForall α a -> do                                               -- ∀App
    α̂ <- fresh
    appType (ctx ++ [CUns α̂])
            (substType (TExt α̂) α a) -- [α̂/a]A
            e
  TExt α̂      -> do                                               -- α̂App
    α̂₁ <- fresh
    α̂₂ <- fresh
    let (ctxL, ctxR) = splitCtx ctx (CUns α̂)
        extCtx = mconcat  -- Γ[α̂₂,α̂₁,α̂ = α̂₁ → α̂₂]
            [ ctxL
            , [ CUns α̂₂
              , CUns α̂₁
              , CSol α̂ (MTExt α̂₁ :-< MTExt α̂₂)
              ]
            , ctxR
            ]
    (TExt α̂₂, ) <$> check extCtx e (TExt α̂₁)
  a :-> c     -> (c, ) <$> check ctx e a                          -- →App
  _           -> die


-----------------------------------------------------------------------
-- Util

-- | Any use of 'die' is a possibility for good error reporting!
die :: HasCallStack => a
die = error "error"
