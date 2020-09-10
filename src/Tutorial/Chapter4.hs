{-@ LIQUID "--short-names"         @-}
{-@ LIQUID "--no-termination"      @-}
{-@ LIQUID "--scrape-used-imports" @-}

module Tutorial.Chapter4 
   ( safeLookup
   , unsafeLookup
   , vectorSum, vectorSum'
   , absoluteSum, absoluteSum'
   , dotProduct
   , sparseProduct, sparseProduct'
   , head, head', head''
   ) where

import Prelude      hiding (abs, head, length)
import Data.List    (foldl')
import Data.Vector  hiding (head, foldl')

{-}
twoLangs = fromList ["haskell", "javascript"]

eeks = [ok, yup, nono]
    where
        ok = twoLangs ! 0
        yup = twoLangs ! 1
        nono = twoLangs ! 3

-- define the size
measure vlen :: Vector a -> Int

-- compute the size
assume length :: x:Vector a -> {v:Nat | v = len v}

-- lookup at index
assume (!) :: x:Vector a -> {v:Nat | v < vlen x} -> a

-}

{-@ type VectorN a N = {v:Vector a | vlen v == N} @-}

{-@ twoLangs :: VectorN String 2 @-}
twoLangs = fromList ["haskell", "javascript"]

{-@ type Btwn Lo Hi = {v:Int | Lo <= v && v < Hi} @-}

-- (!) :: x:Vector a -> Btwn 0 (vlen x) -> a

{-@ fail head @-}
head :: Vector a -> a
head vec = vec ! 0

{-@ type NEVector a = {v:Vector a | 0 < vlen v} @-}

{-@ head' :: NEVector a -> a @-}
head' vec = vec ! 0

-- Exercise 4.1

head'' :: Vector a -> Maybe a
head'' vec = if length vec == 0
                then Nothing
                else Just $ head' vec

-- Exercise 4.2

{-@ unsafeLookup :: n:Nat -> {v:Vector a | n < vlen v} -> a @-}
unsafeLookup index vec = vec ! index

-- Exercise 4.3

{-@ safeLookup :: Vector a -> Int -> Maybe a @-}
safeLookup x i
    | ok        = Just (x ! i)
    | otherwise = Nothing
    where
        ok = 0 <= i && i < length x

--

-- >>> vectorSum (fromList [1, -2, 3])
-- 2
--
vectorSum :: Vector Int -> Int
vectorSum vec = go 0 0
    where
        go acc i
            | i < sz    = go (acc + (vec ! i)) (i + 1)
            | otherwise = acc
        sz = length vec

-- Exercise 4.4

-- Complaints with the i in vec ! i

-- Exercise 4.5

{-@ abs :: Int -> Nat @-}
abs :: Int -> Int
abs x = if x >= 0 then x else -x

-- >>> absoluteSum' (fromList [1, -2, 3])
-- 6
--
{-@ absoluteSum :: Vector Int -> Nat @-}
absoluteSum :: Vector Int -> Int
absoluteSum vec = go 0 0
    where
        go acc i
            | i < sz    = go (acc + abs (vec ! i)) (i + 1)
            | otherwise = acc
        sz = length vec

-- Exercise 4.6

-- Because the "otherwise" branch is equivatent to i == sz

--

loop :: Int -> Int -> a -> (Int -> a -> a) -> a
loop lo hi base f = go base lo
    where
        go acc i
            | i < hi    = go (f i acc) (i + 1)
            | otherwise = acc

vectorSum' :: Vector Int -> Int
vectorSum' vec = loop 0 n 0 body
    where
        body i acc = acc + (vec ! i)
        n          = length vec

-- Exercise 4.7

-- >>> absoluteSum' (fromList [1, -2, 3])
-- 6
--
{-@ absoluteSum' :: Vector Int -> Nat @-}
absoluteSum' vec = loop 0 n 0 body
    where
        body i acc = acc + abs (vec ! i)
        n          = length vec

-- Exercise 4.8

-- >>> dotProduct (fromList [1, 2, 3]) (fromList [4, 5, 6])
-- 32
--
{-@ dotProduct :: x:Vector Int -> y:{v:Vector Int | vlen x == vlen v} -> Int @-}
dotProduct :: Vector Int -> Vector Int -> Int
dotProduct x y = loop 0 sz 0 body
    where
        body i acc = acc + (x ! i) * (y ! i)
        sz         = length x

--

{-@ type SparseN a N = [(Btwn 0 N, a)] @-}

{-@ sparseProduct :: x:Vector _ -> SparseN _ (vlen x) -> _ @-}
sparseProduct :: Vector Int -> [(Int, Int)] -> Int
sparseProduct x y = go 0 y
    where
        go n []          = n
        go n ((i, v):y') = go (n + (x ! i) * v) y'

{-@ sparseProduct' :: x:Vector _ -> SparseN _ (vlen x) -> _ @-}
sparseProduct' :: Vector Int -> [(Int, Int)] -> Int
sparseProduct' x y = foldl' body 0 y
    where
        body sum (i, v) = sum + (x ! i) * v