{-@ LIQUID "--short-names"    @-}
{-@ LIQUID "--no-termination" @-}

module Tutorial.Chapter5 
    ( Sparse(..)
    , okSP, badSP, test1, test2
    , fromList
    ) where

import Data.List (foldl', sort)
import Data.Maybe (fromJust)
import Data.Vector hiding (foldl', fromList, (++))

data Sparse a = SP { spDim   :: Int
                   , spElems :: [(Int, a)] }
    deriving Show

{-@ type Nat = {v:Int | 0 <= v}                   @-}
{-@ type Btwn Lo Hi = {v:Int | Lo <= v && v < Hi} @-}

{-@ data Sparse a = SP { spDim :: Nat
                       , spElems :: [(Btwn 0 spDim, a)] } @-}

{- generated internal representation

data Sparse a where
    SP :: spDim: Nat
       -> spElems:[(Btwn 0 spDim, a)]
       -> Sparse a 
-}

okSP = SP 5 [ (0, "cat")
            , (3, "dog") ]

{-@ fail badSP @-}
badSP = SP 5 [ (0, "cat")
             , (6, "dog") ]

{-@ type SparseN a N = {v:Sparse a | spDim v == N} @-}

{-@ dotProd :: x:Vector Int -> SparseN Int (vlen x) -> Int @-}
dotProd :: Vector Int -> Sparse Int -> Int
dotProd x (SP _ y) = go 0 y
    where
        go sum ((i, v) : y') = go (sum + (x ! i) * v) y'
        go sum []            = sum

{-@ dotProd' :: x:Vector Int -> SparseN Int (vlen x) -> Int @-}
dotProd' :: Vector Int -> Sparse Int -> Int
dotProd' x (SP _ y) = foldl' body 0 y
    where
        body sum (i, v) = sum + (x ! i) * v

-- Exercise 5.1

{-@ fromList :: dim:Int -> [(Int, a)] -> Maybe (SparseN a dim) @-}
fromList :: Int -> [(Int, a)] -> Maybe (Sparse a)
fromList dim elts = 
    if (dim < 0) 
        then Nothing 
        else fmap (SP dim) (traverse tr elts)
                where
                    tr (i, v) = if (0 <= i) && (i < dim) 
                                    then Just (i, v) 
                                    else Nothing

{- This should work (I think) but LH refuses
fromList dim elts = do
    guard (dim >= 0)
    elts' <- traverse tr elts
    return $ SP dim elts'
    where tr (i, v) = if (0 <= i) && (i < dim) 
                                    then Just (i, v) 
                                    else Nothing
-}

-- >>> fromList 3 [(0, "cat"), (2, "mouse")]
-- Just (SP {spDim = 3, spElems = [(0,"cat"),(2,"mouse")]})
--

{-@ test1 :: SparseN String 3 @-}
test1 :: Sparse String
test1 = fromJust $ fromList 3 [(0, "cat"), (2, "mouse")]

-- Exercise 5.2

{-@ plus :: x:Sparse a -> SparseN a (spDim x) -> SparseN a (spDim x) @-}
plus :: (Num a) => Sparse a -> Sparse a -> Sparse a
plus (SP dim x) (SP _ y) = SP dim (merge x y)
    where -- supposes ordered spElems !!!
        merge [] y = y
        merge x [] = x
        merge x@((i, v):x') y@((j, w):y')
            | i < j  = (i, v) : merge x' y
            | i == j = (i, v + w) : merge x' y'
            | i > j  = (j, w) : merge x y'

{- crude but also works
plus (SP dim x) (SP _ y) = SP dim (x ++ y)
-}

{-@ test2 :: SparseN Int 3 @-}
test2 :: Sparse Int
test2 = plus vec1 vec2
    where
        vec1 = SP 3 [(0, 12), (2, 9)]
        vec2 = SP 3 [(0, 8), (1, 100)]

-- >>> test2
-- SP {spDim = 3, spElems = [(0,20),(1,100),(2,9)]}
--
