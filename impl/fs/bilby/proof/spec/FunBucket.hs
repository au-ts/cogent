module FunBucket (
  module FunBucket
, module TypBucket  
) where

import TypBucket

count :: [a] -> Int  -- 'b word
count = length
