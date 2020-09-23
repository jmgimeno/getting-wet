{-@ LIQUID "--no-termination" @-}
{-@ LIQUID "--short-names"    @-}

module Book.Chapter6 where

import Prelude hiding(head, tail, null, foldl1, foldl, sum)

-- Old definitions

{-@ type Nat     = {v:Int | 0 <= v} @-}
{-@ type Pos     = {v:Int | 0 <  v} @-}
{-@ type NonZero = {v:Int | 0 /= v} @-}

{-@ die :: {v:_ | false} -> a @-}
die msg = error msg

--

{-@ divide :: Int -> NonZero -> Int @-}
divide :: Int -> Int -> Int
divide _ 0 = die "divide-by-zero"
divide x n = x `div` n

avg2 x y   = divide (x + y)     2
avg3 x y z = divide (x + y + z) 3

size :: [a] -> Int
size []     =  0
size (_:xs) =  1 + size xs

{-@ ignore avgMany @-}
avgMany xs = divide total elems
  where
    total  = sum  xs
    elems  = size xs

notEmpty :: [a] -> Bool
notEmpty []    = False
notEmpty (_:_) = True

{-@ measure notEmpty @-}

{-@ type NEList a = {v:[a] | notEmpty v} @-}

{-@ size :: xs:[a] -> {v:Nat | notEmpty xs => v > 0} @-}

{-@ average :: NEList Int -> Int @-}
average xs = divide total elems
  where
    total  = sum xs
    elems  = size xs

-- Exercise 6.1

average'      :: [Int] -> Maybe Int
average' xs
  | ok        = Just $ divide (sum xs) elems
  | otherwise = Nothing
  where
    elems     = size xs
    ok        = notEmpty xs -- elems /= 0

-- Exercise 6.2

{-@ ignore size1 @-}
{-@ size1 :: xs:NEList a -> Pos @-}
size1 :: [a] -> Int
size1 []     =  0
size1 (_:xs) =  1 + size1 xs -- cannot guarantee the precondition

{-@ ignore size2 @-}
{-@ size2    :: xs:[a] -> {v:Int | notEmpty xs => v > 0} @-}
size2 :: [a] -> Int
size2 []     =  0
size2 (_:xs) =  1 + size2 xs -- if xs is empty we know nothing about the result

--

{-@ head :: NEList a -> a @-}
head (x:_) = x
head []    = die "Fear not! 'twill ne'er come to pass"

{-@ tail :: NEList a -> [a] @-}
tail (_:xs) = xs
tail []     = die "Relaxeth! this too shall ne'er be"

-- Exercise 6.3

safeHead      :: [a] -> Maybe a
safeHead xs
  | null xs   = Nothing
  | otherwise = Just $ head xs

{-@ null :: xs:[a] -> {v:Bool | v <=> not notEmpty xs } @-}
null :: [a] -> Bool
null []    =  True
null (_:_) =  False

--

{-@ groupEq :: (Eq a) => [a] -> [NEList a] @-}
groupEq []     = []
groupEq (x:xs) = (x:ys) : groupEq zs
  where
    (ys, zs)   = span (x ==) xs

-- >>> eliminateStutter "ssstringssss liiiiiike thisss"
-- "strings like this"
--
eliminateStutter xs = map head $ groupEq xs

{-@ foldl1 :: (a -> a -> a) -> NEList a -> a @-}
foldl1 f (x:xs) = foldl f x xs
foldl1 _ []     = die "foldl1"

foldl :: (a -> b -> a) -> a -> [b] -> a
foldl _ acc []     = acc
foldl f acc (x:xs) = foldl f (f acc x) xs

{-@ sum :: (Num a) => NEList a -> a  @-}
sum []  = die "cannot add up empty list"
sum xs  = foldl1 (+) xs

sumOk  = sum [1,2,3,4,5]    -- is accepted by LH, but

{-@ fail sumBad @-}
sumBad = sum []             -- is rejected by LH

-- Exercise 6.4

{-@ wtAverage :: NEList (Pos, Pos) -> Int @-}
wtAverage :: [(Int, Int)] -> Int
wtAverage wxs = divide totElems totWeight
  where
    elems     = map' (\(w, x) -> w * x) wxs
    weights   = map' (\(w, _) -> w    ) wxs
    totElems  = sum elems
    totWeight = sum weights
    sum       = foldl1 (+)

{-@ map' :: (a -> b) -> NEList a -> NEList b @-}
map' :: (a -> b) -> [a] -> [b]
map' _ []     =  die "Never is never"
map' f [x]    =  [f x]
map' f (x:xs) =  f x : map' f xs

-- Exercise 6.5

{-@ risers :: (Ord a) => xs:[a] -> {ys:[[a]] | notEmpty xs => notEmpty ys} @-}
risers :: (Ord a) => [a] -> [[a]]
risers []     = []
risers [x]    = [[x]]
risers (x:y:etc)
  | x <= y    = (x:s) : ss
  | otherwise = [x] : (s : ss)
    where
      (s, ss) = safeSplit $ risers (y:etc)

{-@ safeSplit :: xs:NEList a -> (a, {ys:[a] | len ys == len xs - 1}) @-}
safeSplit :: [a] -> (a, [a])
safeSplit (x:xs) = (x, xs)
safeSplit _      = die "don't worry, be happy"