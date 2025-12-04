{-# OPTIONS --erasure --rewriting #-}

module index where

-- This is an verified implementation of the coverage checking algorithm 𝒰rec presented in the paper "Warnings for pattern matching" by Luc Maranget.
-- Typechecked using Agda 2.8.0, agda2hs 1.4, and agda-stdlib 2.3.

-- The root module of the verified implementation.
import CoverageCheck

-- Test cases for the coverage checking algorithm.
import Tests
