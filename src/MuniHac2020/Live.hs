module MuniHac2020.Live where

import Prelude hiding (tail, take)

{-@ ex1 :: { i : Int | i >= 60 && i < 105 } @-}
ex1 :: Int
ex1 = 61

{-@ x :: { xs : [ { i : Int | i == 2 } ] | len xs == 5 } @-}
x :: [Int]
x = replicate 5 2

{-@ tail :: { xs : [a] | len xs > 0} -> { ys : [a] | len ys == len xs - 1 } @-}
tail :: [a] -> [a]
tail (_ : xs) = xs
tail _ = impossible "impossisble: tail on empty list" -- to satisfy exhaustive patterns

{-@ impossible :: { s: String | False } -> a @-}
impossible :: String -> a
impossible message = error message

{-@ example :: { xs : [a] | len xs >= 3 } -> [a] @-}
example :: [a] -> [a]
example xs = tail (tail (tail xs))

{-@ type Nat' = { n : Int | n >= 0 } @-} -- Nat defined in Prelude

{-@ type GT N = { n : Int | n >= N } @-}

{-@ inline min @-}
min :: Int -> Int -> Int
min x y = if x <= y then x else y

--{-@ take :: n : Nat ->  { xs : [a] | len xs >= n } -> {rs: [a] | len rs = n } @-}
{-@ take :: n : Nat ->  xs : [a] -> { rs: [a] | len rs == min n (len xs) } @-}
take :: Int -> [a] -> [a]
take i xs
  | i == 0      = []
take i []       = []
take i (x : xs) = x : take (i - 1) xs

data Weekday = Mo | Tu | We | Th | Fr | Sa | Su

{-@ type WeekendDay = { w : Weekday | w == Sa || w == Su} @-}

{-@ weekday :: WeekendDay @-}
weekday :: Weekday
weekday = Su

insert :: Ord a => a -> [a] -> [a]
insert x [] = [x]
insert x (y:ys)
  | x <= y    = x : y : ys
  | otherwise = y : insert x ys

isort :: Ord a => [a] -> [a]
isort = foldr insert []

data SortedList a = Nil | a :<= SortedList a
infixr 5 :<=

-- LH (right now) needs to use record notation
{-@ data SortedList a = Nil | (:<=) { hd :: a, tl :: SortedList { x : a | hd <= x } } @-}

exampleSorted :: SortedList Int
exampleSorted = 2 :<= 3 :<= 4 :<= Nil

insert' :: Ord a => a -> SortedList a -> SortedList a
insert' x Nil = x :<= Nil
insert' x (y :<= ys)
  | x <= y    = x :<= y :<= ys
  | otherwise = y :<= insert' x ys

{- this monomorphic version does not work (b/c we instantiate the a in the refine type which
   bounds the elements of the list) 
   
insert'' :: Int -> SortedList Int -> SortedList Int
insert'' x Nil = x :<= Nil
insert'' x (y :<= ys)
  | x <= y    = x :<= y :<= ys
  | otherwise = y :<= insert'' x ys

-}

{-@ insert'' :: forall < p :: Int -> Bool > . Int<p> -> SortedList (Int<p>) -> SortedList (Int<p>) @-}
insert'' :: Int -> SortedList Int -> SortedList Int
insert'' x Nil = x :<= Nil
insert'' x (y :<= ys)
  | x <= y    = x :<= y :<= ys
  | otherwise = y :<= insert'' x ys

{-@ assume plus :: x : Int -> y : Int -> { z : Int | z = x + y } @-}
plus :: Int -> Int -> Int
plus = (+)

--{-@ isort' :: Ord a => xs : [a] -> { rs : SortedList a | len rs == len xs} @-}
-- current foldr cannot prove, we need:
--  * define lentgth for SortedList
--  * prove that insert increments length
--  * define a foldr that has induction principle that propagates the invariant

isort' :: Ord a => [a] -> SortedList a
isort' = foldr insert' Nil

{-@ type SortedList' a = [a]<{\ x y -> x <= y }> @-} -- in a cons x is the head and y an element of tail

{-@ example' :: SortedList' Integer @-}
example' :: [Integer]
example' = [1, 4, 5]

-- We have to say the termination function that decreases
-- In this case [ len xs, len ys ] also works

{-@ merge :: Ord a => xs : SortedList' a -> ys : SortedList' a -> SortedList' a / [ len xs + len ys ] @-}
merge :: Ord a => [a] -> [a] -> [a]
merge [] ys = ys
merge xs [] = xs
merge (x : xs) (y : ys)
  | x <= y    = x : merge xs (y : ys)
  | otherwise = y : merge (x : xs) ys

{-@ msort :: Ord a => [a] -> SortedList' a @-}
msort :: Ord a => [a] -> [a]
msort [] = []
msort [x] = [x]
msort xs =
  case split xs of -- splitAt (length xs `div` 2) xs
    (ys, zs) -> merge (msort ys) (msort ys)

{-@ split :: xs : [a]  
          -> { r : ([a], [a]) | (len (fst r) + len (snd r) == len xs) 
                                  && ((len xs >= 2) => (len (fst r) > 0) 
                                                          && (len (snd r) > 0)) } @-}
split :: [a] -> ([a], [a])
split [] = ([], [])
split [x] = ([x], [])
split (a : b : rs) = (a : as, b : bs)
  where
    (as, bs) = split rs
