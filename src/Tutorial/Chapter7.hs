{-@ LIQUID "--short-names"    @-}
{-@ LIQUID "--no-termination" @-}

module Tutorial.Chapter7 where
  
import Prelude  hiding  (map, zipWith, zip, drop, take, reverse)

{-@ type TRUE = {v:Bool | v} @-}

{-@ die :: {v:_ | false} -> a @-}
die msg = error msg

data Vector a = V { vDim :: Int
                  , vElts :: [a]
                  }

data Matrix a = M { mRow :: Int
                  , mCol :: Int
                  , mElts :: Vector (Vector a)
                  }

{-@ ignore dotProd @-}
dotProd :: (Num a) => Vector a -> Vector a -> a
dotProd vx vy = sum (prod xs ys)
  where
    prod = zipWith (*)
    xs   = vElts vx
    ys   = vElts vy

-- {-@ ignore matProd @-}
-- Wrong definition
matProd :: (Num a) => Matrix a -> Matrix a -> Matrix a
matProd (M rx _ xs) (M _ cy ys) = M rx cy elts
  where
    elts  = for xs (\xi ->
              for ys (\yj ->
                dotProd xi yj
              )
            )

-- {-@ ignore for @-}
for :: Vector a -> (a -> b) -> Vector b
for (V n xs) f = V n (map f xs)

{-@ measure size @-}
{-@ size :: [a] -> Nat @-}
size :: [a] -> Int
size []     = 0
size (_:rs) = 1 + size rs

{- generated translation

data [a] where
  []  :: {v:[a] | size v == 0}
  (:) :: a -> xs:[a] -> {v:[a] | size v = 1 + size xs}
-}

{-@ measure notEmpty @-}
notEmpty :: [a] -> Bool
notEmpty []    = False
notEmpty (_:_) = True

{- generated code conjoinning measures

data [a] where
  []  :: {v:[a] | not (NotEmpty v) && size v == 0}
  (:) :: a -> xs:[a] -> {v:[a] | notEmpty v && size v = 1 + size xs}
-}

type List a = [a]

{-@ type ListN a N = {v:List a | size v == N} @-}
{-@ type ListX a X = ListN a {size X}         @-}

-- Exercise 7.1

{-@ map :: (a -> b) -> xs:List a -> ListX b xs @-}
map _ []     = []
map f (x:xs) = f x : map f xs

{-@ prop_map :: List a -> TRUE @-}
prop_map xs = size ys == size xs
  where
    ys = map id xs

-- Exercise 7.2

{-@ reverse :: xs:List a -> ListX a xs @-}
reverse xs = go [] xs
  where
    {-@ go :: xs:List a -> ys:List a -> ListN a {size xs + size ys} @-}
    go acc []     = acc
    go acc (x:xs) = go (x:acc) xs

--

{-@ zipWith :: (a -> b -> c) -> xs:List a
                             -> ListX b xs
                             -> ListX c xs
  @-}
zipWith f (a:as) (b:bs) = f a b : zipWith f as bs
zipWith _ [] [] = []
zipWith _ _  _  = die "no other cases"

{-@ predicate Tinier X Y Z = Min (size X) (size Y) (size Z) @-}
{-@ predicate Min X Y Z = (if Y < Z then X == Y else X == Z)  @-} -- They use = but I prefer == (it seems 'healthier')

{-@ zip :: as:[a] -> bs:[b] -> {v:[(a,b)] | Tinier v as bs} @-}
zip (a:as) (b:bs) = (a, b) : zip as bs
zip [] _          = []
zip _  []         = []

-- Exercise 7.3

{-@ zipOrNull :: as:[a] 
              -> bs:[b] 
              -> {v:[(a, b)] | ((size as == 0 || size bs == 0) => size v == 0)
                                && ((size as /= 0 && size bs /= 0) => Tinier v as bs)} 
  @-}
zipOrNull       :: [a] -> [b] -> [(a, b)]
zipOrNull [] _  = []
zipOrNull _ []  = []
zipOrNull xs ys = zip xs ys

{-@ test1 :: {v: _ | size v == 2} @-}
test1     = zipOrNull [0, 1] [True, False]

{-@ test2 :: {v: _ | size v == 0} @-}
test2     = zipOrNull [] [True, False]

{-@ test3 :: {v: _ | size v == 0} @-}
test3     = zipOrNull ["cat", "dog"] []

{-@ type ListGE a N = {v:List a | N <= size v} @-}

{-@ take' :: n:Nat -> ListGE a n -> ListN a n @-}
take' :: Int -> [a] -> [a]
take' 0 _      = []
take' n (x:xs) = x : take' (n - 1) xs
take' _ _      = die "won't happen"

-- Exercise 7.4

{-@ drop :: n:Nat -> as:ListGE a n -> v:ListN a {size as - n} @-}
drop :: Int -> [a] -> [a]
drop 0 xs     = xs
drop n (_:xs) = drop (n-1) xs
drop _ _      = die "won't happen"

{-@ test4 :: ListN String 2 @-}
test4 = drop 1 ["cat", "dog", "mouse"]

-- Exercise 7.5

{-@ take :: n:Nat -> as:List a -> {v:List a | Min (size v) n (size as)} @-}
take :: Int -> [a] -> [a]
take 0 _       = []
take _ []      = []
take n (x:xs)  = x : take (n-1) xs

{-@ test5 :: [ListN String 2] @-}
test5 = [ take 2  ["cat", "dog", "mouse"]
        , take 20 ["cow", "goat"]        ]

--

{-@ measure fst @-}
fst  (x, _) = x

{-@ measure snd @-}
snd (_, y) = y

{-@ predicate Sum2 X N = size (fst X) + size (snd X) == N @-}

{-@ partition :: _ -> xs:_ -> {v:_ | Sum2 v (size xs)} @-}
partition :: (a -> Bool) -> [a] -> ([a], [a])
partition _ []     = ([], [])
partition f (x:xs)
  | f x            = (x:ys, zs)
  | otherwise      = (ys, x:zs)
  where
    (ys, zs)       = partition f xs

{-@ append :: xs:[a] -> ys:[a] -> {v:[a] | size xs + size ys == size v} @-}
append :: [a] -> [a] -> [a]
append xs []     = xs
append [] ys     = ys
append (x:xs) ys = x : append xs ys

{-@ quickSort :: (Ord a) => xs:List a -> ListX a xs @-}
quickSort :: (Ord a) => [a] -> [a]
quickSort []     = []
quickSort (x:xs) = append (quickSort lesser) (x : quickSort greater)
  where
    (lesser, greater) = partition (<x) xs

-- >>> quickSort [1,4,3,2]
-- [1,2,3,4]
--

{-@ test10 :: ListN String 2 @-}
test10 = quickSort (drop 1 ["cat", "dog", "mouse"])

--

{-@ data Vector a = V { vDim :: Nat
                      , vElts :: ListN a vDim }
  @-}

--{-@ vDim :: x:_ -> {v:Nat | v == vDim x } @-} 

okVec  = V 2 [10, 20]

{-@ fail badVec @-}
badVec = V 2 [10, 20, 30]

-- | Non-Empty Vectors

{-@ type VectorNE a = {v:Vector a | vDim v > 0} @-}

-- | Vectors of size N

{-@ type VectorN a N = {v:Vector a | vDim v == N} @-}

-- | Vectors of Size Equal to Another Vector X

{-@ type VectorX a X = VectorN a {vDim X} @-}

{-@ vEmp :: VectorN a 0 @-}
vEmp = V 0 []

{-@ vCons :: a -> x:Vector a -> VectorN a {vDim x + 1} @-}
vCons x (V n xs) = V (n + 1) (x : xs)

{-@ vHd :: VectorNE a -> a @-}
vHd (V _ (x:_)) = x
vHd _           = die "nope"

{-@ vTl :: x:VectorNE a -> VectorN a {vDim x - 1} @-}
vTl (V n (_:xs)) = V (n - 1) xs
vTl _            = die "nope"

{-@ for :: x:Vector a -> (a -> b) -> VectorX b x @-}
-- for (V n xs) f = V n (map f xs)

{-@ vBin :: (a -> b -> c) 
         -> x:Vector a
         -> VectorX b x
         -> VectorX c x
  @-}
vBin op (V n xs) (V _ ys) = V n (zipWith op xs ys)

{-@ dotProduct :: (Num a) => x:Vector a -> VectorX a x -> a @-}
dotProduct x y = sum $ vElts $ vBin (*) x y

-- Exercise 7.7

{-@ vecFromList :: x:[a] -> VectorN a {size x} @-}
vecFromList :: [a] -> Vector a
vecFromList xs = V (size xs) xs

test6 = dotProduct vx vy
  where
    vx = vecFromList [1, 2, 3]
    vy = vecFromList [4, 5, 6]

-- Exercise 7.8

{-@ flatten :: n:Nat
            -> m:Nat
            -> VectorN (VectorN a m) n
            -> VectorN a {m * n}
  @-}
flatten :: Int -> Int -> Vector (Vector a) -> Vector a
flatten = undefined
--flatten n m (V _ xs) = V (m * n) (foldr append [] (map vElts xs))

--

{-@ product :: xs:Vector _
            -> ys:Vector _
            -> VectorN _ {vDim xs * vDim ys}
  @-}
product xs ys = flatten (vDim ys) (vDim xs) xys
  where
    xys = for ys $ \y ->
            for xs $ \x ->
              x * y

