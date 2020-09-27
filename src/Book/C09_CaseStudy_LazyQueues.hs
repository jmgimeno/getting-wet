{-@ LIQUID "--no-termination" @-}
{-@ LIQUID "--maxparams=3"    @-}

module Book.C09_CaseStudy_LazyQueues 
  (Queue, remove, emp, realSize)
  where

import Prelude hiding (replicate, take, length)

{-@ die :: {v:String | false} -> a @-}
die x = error x

{-@ invariant {v:SList a | size v >= 0} @-}

data SList a = SL { size :: Int, elems :: [a] }

{-@ measure realSize @-}
realSize :: [a] -> Int
realSize [] = 0
realSize (_:xs) = 1 + realSize xs

{-@ data SList a = SL {
      size  :: Nat
    , elems :: {v:[a] | realSize v == size}
    } 
  @-}

okList = SL 1 ["cat"]

{-@ fail badList @-}
badList = SL 1 []

{-@ type SListN a N = {v:SList a | size v == N} @-}

{-@ nil :: SListN a 0 @-}
nil = SL 0 []

{-@ cons :: a -> xs:SList a -> SListN a {size xs + 1} @-}
cons x (SL n xs) = SL (n + 1) (x : xs)

-- Exercise 9.1

{-@ tl :: {xs:SList a | size xs > 0} -> SListN a {size xs - 1} @-}
tl (SL n (_:xs))  = SL (n - 1) xs
tl _             = die "empty SList"

{-@ hd :: {xs:SList a | size xs > 0} -> a @-}
hd (SL _ (x:_)) = x
hd _            = die "empty SList"

{-@ okList :: SListN String 1 @-}
okHd = hd okList

{-@ fail badHd @-}
badHd = hd (tl okList)

{-@ type SListLE a N = {v:SList a | size v <= N} @-}

{-@ data Queue a = Q {
      front :: SList a
    , back  :: SListLE a (size front)
    }
  @-}
data Queue a = Q {
    front :: SList a
  , back  :: SList a
}

okQ = Q okList nil

{-@ fail badQ @-}
badQ = Q nil okList

emp = Q nil nil

remove (Q f b) = (hd f, makeq (tl f) b)

-- Exercise 9.2

-- Via pattern matching we do not use the refined signatures of hd & tl

-- Exercise 9.3

{-@ measure qSize @-}
qSize (Q f b) = size f + size b

{-@ type QueueN a N ={v:Queue a | qSize v == N} @-}

okRemove = remove example2Q

{-@ fail badRemove @-}
badRemove = remove example0Q

{-@ emp :: QueueN _ 0 @-}

{-@ example2Q :: QueueN _ 2 @-}
example2Q = Q (1 `cons` (2 `cons`nil)) nil

{-@ example0Q :: QueueN _ 0 @-}
example0Q = Q nil nil

{-@ remove :: {v:Queue a | qSize v > 0} -> (a, QueueN a {qSize v - 1}) @-}

--

insert e (Q f b) = makeq f (e `cons` b)

-- Exercise 9.4

{-@ insert :: a -> q:Queue a -> QueueN a {qSize q + 1} @-}

{-@ replicate :: n:Nat -> a -> QueueN a n @-}
replicate :: Int -> a -> Queue a
replicate 0 _ = emp
replicate n x = insert x (replicate (n - 1) x)

{-@ okReplicate :: QueueN _ 3 @-}
okReplicate = replicate 3 "Yeah!"

{-@ fail badReplicate @-}
{-@ badReplicate :: QueueN _ 3 @-}
badReplicate = replicate 1 "No!"

--

{- 
  invariant: size f >= size b
  we call makeq with f' = (tl f) and b
  so (size f' = size f - 1) => size f = size f' + 1
  so size f' + 1 >= size b
-}

{-@ makeq :: f:SList a 
          -> b:SListLE a {size f + 1} 
          -> QueueN a {size f + size b} @-}
makeq f b
  | size b <= size f = Q f b
  | otherwise        = Q (rot f b nil) nil -- size f < size b

-- Exercise 9.5

{- size b <= size f + 1 && size f < size b => size b = size f + 1 -}

{-@ rot :: f:SList a 
        -> b:SListN a {size f + 1} 
        -> acc:SList a 
        -> SListN a {size f + size b + size acc} 
  @-}
rot f b acc
  | size f == 0 = hd b `cons` acc
  | otherwise   = hd f `cons`rot (tl f) (tl b) (hd b `cons` acc)

-- Exercise 9.6

{-@ type QueueGE a N = {v:Queue a | qSize v >= N} @-}

{-@ take :: n:Nat 
         -> q:QueueGE a n
         -> (QueueN a n, QueueN a {qSize q - n})
  @-}
take :: Int -> Queue a -> (Queue a, Queue a)
take 0 q = (emp, q)
take n q = (insert x out, q'')
  where
    (x, q')    = remove q
    (out, q'') = take (n - 1) q'

-- NOTE: I've had to strengthen the refinement of remove to assert its size

{-@ okTake :: (QueueN _ 2, QueueN _ 1) @-}
okTake = take 2 exampleQ

{-@ fail badTake @-}
badTake = take 10 exampleQ

exampleQ = insert "nal" $ insert "bob" $ insert "alice" $ emp

