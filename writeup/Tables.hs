module Tables where

import Data.Text (Text)
import qualified Data.Text as T
import qualified Data.Text.IO as T
import Control.Monad
import System.IO
import System.Directory
import System.FilePath.Posix
import Data.List
import Control.Exception

tableMain :: IO ()
tableMain = return ()

data Table = Table
  { tableColumnNames :: [Text]
  , tableColumns :: [(Text, [Text])]
  , tableRows :: [[(Text, Text)]]
  } deriving (Eq, Ord, Show)

tableFromRows :: [Text] -> [[Text]] -> Table
tableFromRows header rows = Table header (zip header $ transpose rows) (map (zip header) rows)

parseTable :: Text -> Either String Table
parseTable s = do
  (rawHeader, separator, rawRows) <- maybeToEither "expecting a header and separator row" $ uncons2 $ T.lines s
  when (not $ T.all (== '=') $ T.strip separator) $
    Left "separator is malformed, should be ^=*$"
  let header = splitDoubleSpace rawHeader
      rows = map splitDoubleSpace rawRows
      hlen = length header
  case foldl' (findViolation hlen) Nothing $ count rows of
    Nothing -> return ()
    Just (l, rowData) -> Left $ "row " ++ show l ++ " is not same length as header"
  return $ tableFromRows header rows
  where
    findViolation _ (Just i) _ = Just i
    findViolation hlen Nothing (l, rowData)
      | length rowData == hlen = Nothing
      | otherwise = Just (l, rowData)

parseTableIO :: FilePath -> IO Table
parseTableIO f = do
  s <- T.readFile f
  case parseTable s of
    Left e -> fail e
    Right a -> return a

checkTable :: Text -> Maybe String
checkTable s = case parseTable s of
  Left msg -> Just msg
  Right _ -> Nothing

checkTableIO :: FilePath -> IO ()
checkTableIO fp = do
  putStrLn $ "checking " ++ fp
  putStr " ... "
  s <- T.readFile fp
  case checkTable s of
    Just msg -> putStrLn $ "BAD " ++ msg
    Nothing -> putStrLn "OK"

printTable_unchecked :: String -> Bool -> Table -> Text
printTable_unchecked delim doHeader (Table columnNames columns rows) =
  let columnWidths :: [Int]
      columnWidths = map (\(hdr, vals) -> maximum $ map T.length $ hdr:vals) columns
      namesWithWidths :: [(Int, Text)]
      namesWithWidths = zip columnWidths columnNames
      rowsWithWidths :: [[(Int, Text)]]
      rowsWithWidths = map (zip columnWidths . map snd) rows
      separatorLen :: Int
      separatorLen = sum columnWidths + 4 * (length columnWidths - 1)

      pheader :: Text
      pheader = T.intercalate (T.pack delim) $ map (uncurry pad) namesWithWidths
      psep :: Text
      psep = T.replicate separatorLen $ T.pack "="
      prows :: [Text]
      prows = map (T.intercalate (T.pack delim)) $ map (map $ uncurry pad) rowsWithWidths
  in T.intercalate (T.pack "\n") $ [pheader] ++ (if doHeader then [psep] else []) ++ prows
    where
      pad :: Int -> Text -> Text
      pad i s = s `T.append` T.replicate (i - T.length s) (T.pack " ")

printTable :: Table -> Text
printTable t =
  let output = printTable_unchecked "    " True t
  in assert (parseTable output == Right t) output

printTableIO :: FilePath -> Table -> IO ()
printTableIO fp t = T.writeFile fp $ printTable t

exportTableIO :: FilePath -> Table -> IO ()
exportTableIO fp t = T.writeFile fp $ printTable_unchecked "\t" False t

alterTableIO :: FilePath -> (Table -> Table) -> IO ()
alterTableIO fp f = do
  t <- parseTableIO fp
  printTableIO fp $ f t

tidyTableIO :: FilePath -> IO ()
tidyTableIO fp = do
  putStrLn $ "checking " ++ fp
  putStr " ... "
  s <- T.readFile fp
  case parseTable s of
    Left msg -> putStrLn $ "BAD " ++ msg
    Right t -> do
      let tp = printTable t
      if (tp /= s)
        then do
          putStrLn "Needs tidyning.  Tidy now? (y/n)"
          let loop = do
                c <- getChar
                case c of
                  'y' -> T.writeFile fp tp
                  'n' -> return ()
                  _ -> loop
          loop
        else putStrLn "OK"

-- Utils {{{

splitDoubleSpace :: Text -> [Text]
splitDoubleSpace = filter (not . T.null) . map T.strip . T.splitOn (T.pack "  ")

maybeToEither :: a -> Maybe b -> Either a b
maybeToEither a Nothing = Left a
maybeToEither _ (Just b) = Right b

uncons :: [a] -> Maybe (a, [a])
uncons [] = Nothing
uncons (x:xs) = Just (x, xs)

uncons2 :: [a] -> Maybe (a, a, [a])
uncons2 xs = do
  (x1, xs') <- uncons xs
  (x2, xs'') <- uncons xs'
  return (x1, x2, xs'')

extendList :: Int -> [a] -> Maybe [Maybe a]
extendList 0 [] = Just []
extendList 0 (_:_) = Just []

allTableFiles :: (FilePath -> IO ()) -> IO ()
allTableFiles action = do
  cd <- getCurrentDirectory
  fps <- liftM (filter (not . isPrefixOf ".")) $ getDirectoryContents cd
  forM_ fps $ \ fp -> do
    de <- doesDirectoryExist fp
    when de $ do
      setCurrentDirectory fp
      allTableFiles action
      setCurrentDirectory ".."
    when (takeExtension fp == ".tbl") $
      action $ cd ++ "/" ++ fp

count :: [a] -> [(Int, a)]
count = countr 1
  where
    countr _ [] = []
    countr i (x:xs) = (i,x) : countr (i+1) xs

permute :: [Int] -> [a] -> [a]
permute [] _ = []
permute (i:is) xs = xs !! i : permute is xs

safeHead :: [a] -> Maybe a
safeHead [] = Nothing
safeHead (x:_) = Just x

-- }}}
