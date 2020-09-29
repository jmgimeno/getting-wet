{-@ LIQUID "--no-termination" @-}
{-@ LIQUID "--short-names"    @-}
{-@ LIQUID "--prune"          @-}

{-# LANGUAGE ForeignFunctionInterface #-}

module Book.C11_CaseStudy_Pointers where

import Data.Word
import Foreign.C.Types
import Foreign.ForeignPtr
import Foreign.Ptr
import Foreign.Storable
import System.IO.Unsafe
import Data.ByteString.Char8 (pack, unpack)
import Data.ByteString.Unsafe (unsafeTake)
import Data.ByteString.Internal (c2w, w2c)

{-@ type TRUE = {v:Bool | v } @-}

{-@ type StringN N = {v:String | len v = N} @-}
{-@ type BNat N    = {v:Nat    | v <= N}    @-}


{-@ ignore chop' @-}
chop' :: String -> Int -> String
chop' s n = s'
  where
    b  = pack s          -- down to low-level
    b' = unsafeTake n b  -- grab n chars
    s' = unpack b'       -- up to high-level

-- >>> let ex = "Ranjit Loves Burritos"
-- >>> chop' ex 10
-- >>> chop' ex 30
-- "Ranjit Lov"
-- "Ranjit Loves Burritos\NUL\NUL\NUL Z\173\DLEB\NUL"
--

{-@ fail zero4 @-}
zero4 = do fp <- mallocForeignPtrBytes 4
           withForeignPtr fp $ \p -> do
             poke (p `plusPtr` 0) zero
             poke (p `plusPtr` 1) zero
             poke (p `plusPtr` 2) zero
             poke (p `plusPtr` 3) zero
           return fp
        where
           zero = 0 :: Word8

{-@ fail zero4' @-}
zero4' = do fp <- mallocForeignPtrBytes 4
            withForeignPtr fp $ \p -> do
              poke (p `plusPtr` 0) zero
              poke (p `plusPtr` 1) zero
              poke (p `plusPtr` 2) zero
              poke (p `plusPtr` 8) zero -- ERROR !!!
            return fp
         where
            zero = 0 :: Word8

--

{-@ type PtrN a N        = {v:Ptr a        | plen v  == N} @-}
{-@ type ForeignPtrN a N = {v:ForeignPtr a | fplen v == N} @-}


{-@ fail zero3 @-}
zero3 = do fp <- mallocForeignPtrBytes 4
           withForeignPtr fp $ \p -> do
             poke (p `plusPtr` 0) zero
             poke (p `plusPtr` 1) zero
             poke (p `plusPtr` 2) zero
           return fp
        where
           zero = 0 :: Word8

{-@ type OkPtr a = {v:Ptr a | 0 < plen v} @-}

