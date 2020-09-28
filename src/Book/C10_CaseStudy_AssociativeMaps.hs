{-@ LIQUID "--short-names"    @-}
{-@ LIQUID "--no-termination" @-}

module Book.C10_CaseStudy_AssociativeMaps where

import Data.Set hiding (elems)

{-@ die :: {v:_ | false} -> a @-}
die x = error x
  
-- | Set Interface
{-@ predicate In X Xs      = Set_mem X Xs               @-}
{-@ predicate Subset X Y   = Set_sub X Y                @-}
{-@ predicate Empty  X     = Set_emp X                  @-}
{-@ predicate Union X Y Z  = X = Set_cup Y Z            @-}
{-@ predicate Union1 X Y Z = Union X (Set_sng Y) Z      @-}

-- | Predicate Aliases
{-@ predicate NoKeys M     = Empty (keys M)             @-}
{-@ predicate HasKey K M   = In K (keys M)              @-}
{-@ predicate AddKey K M N = Union1 (keys N) K (keys M) @-}

--

type Var = String

data Expr = Const Int
          | Var   Var
          | Plus  Expr Expr
          | Let   Var Expr Expr

{-@ measure val @-}
val :: Expr -> Bool
val (Const _)   = True
val (Var _)     = False
val (Plus _ _)  = False
val (Let _ _ _) = False

{-@ type Val = {v:Expr | val v} @-}

{-@ plus :: Val -> Val -> Val @-}
plus (Const i) (Const j) = Const $ i + j
plus _         _         = die "Bad call to plus"

{-@ type Env = Map Var Val @-}

{-@ measure free @-}
free :: Expr -> Set Var
free (Const _)     = empty
free (Var x)       = singleton x
free (Plus e1 e2)  = xs1 `union` xs2
  where
    xs1 = free e1
    xs2 = free e2
free (Let x e1 e2) = xs1 `union` (xs2 `difference`xs)
  where
    xs1 = free e1
    xs2 = free e2
    xs  = singleton x

{-@ type ClosedExpr G = {v:Expr | Subset (free v) (keys G)} @-}

{-@ eval :: g:Env -> ClosedExpr g -> Val @-}
eval _ i@(Const _)   = i
eval g (Var x)       = get x g
eval g (Plus e1 e2)  = plus (eval g e1) (eval g e2)
eval g (Let x e1 e2) = eval g' e2
  where
    g' = set x v1 g
    v1 = eval g e1

{-@ topEval :: {v:Expr | Empty (free v)} -> Val @-}
topEval = eval emp

-- Exercise 10.1

{-@ evalAny :: Env -> Expr -> Maybe Val @-}
evalAny g e
  | ok        = Just $ eval g e
  | otherwise = Nothing
  where
    ok = (free e) `isSubsetOf` (keys g)

{-@ fail tests @-}
tests = [v1, v2]
  where
    v1  = topEval e1   -- Rejected by LH
    v2  = topEval e2   -- Accepted by LH
    e1  = (Var "x") `Plus` c1
    e2  = Let x c10 e1
    x   = "x"
    c1  = Const 1
    c10 = Const 10

-- Exercise 10.2

-- Extend Epr to include functions

-- data Expr = ... | Fun Var Expr | App Expr Expr

-- TODO

--

{-@ data Map k v = Node { key   :: k
                        , value :: v
                        , left  :: Map {v:k | v < key} v
                        , right :: Map {v:k | key < v} v }
                  | Tip
  @-}

data Map k v = Node { key   :: k
                    , value :: v
                    , left  :: Map k v
                    , right :: Map k v }
             | Tip

{-@ measure keys @-}
keys :: (Ord k) => Map k v -> Set k
keys Tip = empty
keys (Node k _ l r) = ks `union` kl `union` kr
  where
    kl = keys l
    kr = keys r
    ks = singleton k

-- Exercise 10.3

{-@ emp :: {m:Map k v | Empty (keys m)} @-}
emp = Tip

-- Exercise 10.4

{-@ set :: (Ord k) => k:k -> v -> m:Map k v 
        -> {n:Map k v | AddKey k m n} @-}
set k' v' (Node k v l r)
  | k == k'   = Node k v' l r
  | k < k'    = Node k v l (set k' v' r)
  | otherwise = Node k v (set k' v' l) r
set k' v' Tip = Node k' v' Tip Tip

--

{-@ fail get' @-}
{-@ get' :: (Ord k) => k:k -> {m:Map k v | HasKey k m} -> v @-}
get' k' m@(Node k v l r)
  | k == k'   = v
  | k' < k    = get k' l
  | otherwise = get k' r
get' _ Tip    = die "Lookup Never Fails"

{-@ lemma_notMem :: key:k
                 -> m:Map {k:k | k /= key} v
                 -> {v:Bool | not (HasKey key m)}
  @-}
lemma_notMem :: k -> Map k v -> Bool
lemma_notMem _   Tip            = True
lemma_notMem key (Node _ _ l r) = lemma_notMem key l && lemma_notMem key r

{-@ get :: (Ord k) => k:k -> {m:Map k v | HasKey k m} -> v @-}
get k' (Node k v l r)
  | k == k'   = v
  | k' < k    = assert (lemma_notMem k' r) $ get k' l
  | otherwise = assert (lemma_notMem k' l) $ get k' r
get _  Tip    = die "Lookup Never Fails"

assert _ x = x

-- Exercise 10.5

{-@ mem :: (Ord k) => k:k -> m:Map k v 
                   -> {v:Bool | v <=> HasKey k m} @-}
mem k' (Node k _ l r)
  | k' == k   = True
  | k' < k    = assert (lemma_notMem k' r) $ mem k' l
  | otherwise = assert (lemma_notMem k' l) $ mem k' r
mem _ Tip     = False

-- Exercise 10.6

{-@ fresh :: xs:[Int] -> {v:Int | not (Elem v xs)} @-}
fresh :: [Int] -> Int
fresh = undefined

{-@ predicate Elem X Ys = In X (elems Ys) @-}
{-@ measure elems @-}
elems []  = empty
elems (x:xs) = singleton x `union` elems xs
