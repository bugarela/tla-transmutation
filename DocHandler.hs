module DocHandler where

import Data.List

moduleDoc [] = []
moduleDoc doc = "@moduledoc \"\"\"\n" ++ (intercalate "\n" (map cleanTrailing doc)) ++ "\n\"\"\"\n"

funDoc [] = []
funDoc doc = "@doc \"\"\"\n" ++ (intercalate "\n" (map cleanTrailing doc)) ++ "\n\"\"\"\n"

comment doc = intercalate "\n" (map (((++) "# ") . cleanTrailing) doc) ++ "\n"

allSpaces s = dropWhile (== ' ') s == []

cleanTrailing [] = []
cleanTrailing (x:xs) =
  if allSpaces xs
    then [x]
    else x : (cleanTrailing xs)
