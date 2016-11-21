{-# LANGUAGE OverloadedStrings #-}

-- | Parser for the Hanoi omega automata format (https://github.com/adl/hoaf)
module OmegaAutomata.Hoa ( AliasName
                         , LabelExpr(..)
                         , HoaAccCond(..)
                         , MinMax(..)
                         , EvenOdd(..)
                         , AccName(..)
                         , HeaderItem(..)
                         , EdgeItem(..)
                         , BodyItem(..)
                         , HOA() , header, body, addProps
                         , parseHoa
                         , toHoa
                         , nbaToHoa, dpaToHoa, draToHoa
                         , hoaToNBA, hoaToDRA, hoaToDPA
                        ) where
import qualified OmegaAutomata.Automata as A
import qualified Data.Text as T
import Data.Attoparsec.Text hiding (string, decimal)
import qualified Data.Attoparsec.Text as DAT
import Data.Attoparsec.Expr
import Control.Applicative
import Control.Monad.State as SM
import Data.List (intersperse)
import qualified Data.Set as S
import Data.List
import qualified Data.Map as M
import Data.Maybe


data HOA = HOA [HeaderItem] [BodyItem]
  deriving Show

header :: HOA -> [HeaderItem]
header (HOA hs bs) = hs

body :: HOA -> [BodyItem]
body (HOA hs bs) = bs

addProps :: [HeaderItem ] -> HOA -> HOA
addProps ps (HOA hs bs) = HOA (hs ++ ps) bs

type AliasName = T.Text

data LabelExpr = LBoolExpr Bool
               | RefAP Int
               | RefAlias AliasName
               | LNot LabelExpr
               | LAnd LabelExpr LabelExpr
               | LOr LabelExpr LabelExpr
               deriving (Show, Eq, Ord)

data HoaAccCond = FinCond Int
                | InfCond Int
                | CompFinCond Int
                | CompInfCond Int
                | AccAnd HoaAccCond HoaAccCond
                | AccOr HoaAccCond HoaAccCond
                | AccBoolExpr Bool
                deriving Show

data MinMax = Min | Max deriving Show

data EvenOdd = Even | Odd deriving Show

data AccName = Buchi
             | GBuchi Int
             | CoBuchi
             | GCoBuchi Int
             | Streett Int
             | Rabin Int
             | GRabin Int [Int]
             | Parity MinMax EvenOdd Int
             | All
             | None
             deriving Show

data HeaderItem = NumStates Int
                | AP [T.Text]
                | Alias (AliasName, LabelExpr)
                | Acceptance (Int, HoaAccCond)
                | Start [Int]
                | Tool [T.Text]
                | Name T.Text
                | Properties [T.Text]
                | AcceptanceName AccName
                deriving Show

data EdgeItem = EdgeItem
                { edgeLabel :: Maybe LabelExpr
                , stateConj :: [Int]
                , accSig :: Maybe [Int]
                }
                deriving Show

data BodyItem = BodyItem
                { stateLabel :: Maybe LabelExpr
                , num :: Int
                , descr :: Maybe T.Text
                , stateAccSig :: Maybe [Int]
                , edges :: [EdgeItem]
                }
                deriving Show

class MBoolExpr a where
  _true :: a
  _false :: a
  _and :: a -> a -> a
  _or :: a -> a -> a

class (MBoolExpr a) => BoolExpr a where
  _not :: a -> a

instance MBoolExpr LabelExpr where
   _true = LBoolExpr True
   _false = LBoolExpr False
   _and = LAnd
   _or = LOr

instance BoolExpr LabelExpr where
  _not = LNot

instance MBoolExpr HoaAccCond where
  _and = AccAnd
  _or = AccOr
  _true = AccBoolExpr True
  _false = AccBoolExpr False
  
-- | The actual parser
--   Returns a tuple of headeritems and bodyitems
parseHoa :: Parser HOA 
parseHoa = do
  whitespace
  parseAttribute "HOA"
  token "v1"
  (hs, (i, as)) <- runStateT (many parseHeaderItem) (0, [])
  token "--BODY--"
  bs <- many $ parseBodyItem i as
  token "--END--"
  return $ HOA hs bs


hoaToEdges :: [BodyItem] -> [(A.State, Maybe LabelExpr, A.State)]
hoaToEdges bs = [(q1, l, q2) | b <- bs
                             , e <- edges b
                             , let q1 = num b
                             , q2 <- stateConj e
                             , let l = edgeLabel e]


hoaToStates :: [BodyItem] -> [(A.State, Maybe LabelExpr)]
hoaToStates bs = [(q,l) | BodyItem l q _ _ _ <- bs]


hoaToStartStates :: [HeaderItem] -> [A.State]
hoaToStartStates hs = concat [qs | Start qs <- hs]


-- | Convert parsed Hoa to NBA.
hoaToNBA :: HOA 
         -> A.NBA A.State (Maybe LabelExpr) (Maybe LabelExpr)
hoaToNBA (HOA hs bs) =
  let aps = concat [aps | AP aps <- hs]
      qs = hoaToStates bs
      ts = hoaToEdges bs
      ss = hoaToStartStates hs
      as = [q | BodyItem _ q _ (Just _) _ <- bs]
  in

      (A.makeNBA qs ts ss as) { A.aps = Just $ aps }

      
buchitoparity :: [(A.State, Maybe LabelExpr)] -> HOA -> A.ParityAccept A.State
buchitoparity qs (HOA hs bs) =
    let infs = [q | BodyItem _ q _ (Just _) _ <- bs]
        parmap = M.fromList $
            map (\(q,_) -> (q, if q `elem` infs then 0 else 1 ))
            $ qs
    in A.MinEv parmap
      
paracc :: MinMax -> EvenOdd -> Int -> HOA -> A.ParityAccept A.State
paracc mm eo i (HOA hs bs) = 
     let accn = case (mm,eo) of
                            (Max, Even) -> A.MaxEv
                            (Max, Odd) -> A.MaxOdd
                            (Min, Even) -> A.MinEv
                            (Min, Odd) -> A.MinOdd
     in  accn $ M.fromList $ do
            BodyItem _ q _ (Just [i]) _ <- bs
            return (q, i)

rabin1toparity :: HOA -> A.ParityAccept A.State
rabin1toparity (HOA hs bs) =
    let [(accl, accr)] = [(accl, accr) | Acceptance (2, AccAnd accl accr)  <- hs ]
        fin = case (accl, accr) of
                   (FinCond 0, InfCond 1) -> 0
                   (FinCond 1, InfCond 0) -> 1
                   (InfCond 0, FinCond 1) -> 1
                   (InfCond 1, FinCond 0) -> 0
        topar f mi = case mi of
                          Nothing -> 0
                          Just [i] -> if i == f then 2 else 1
    in A.MaxOdd $ M.fromList $ do
            BodyItem _ q _ mi _ <- bs
            return (q, topar fin mi)
            
alltoparity :: HOA -> A.ParityAccept A.State
alltoparity (HOA _ bs) = A.MaxEv $ M.fromList $ zip [q | BodyItem _ q _ _ _ <- bs] (repeat 0)
            
nonetoparity :: HOA -> A.ParityAccept A.State
nonetoparity (HOA _ bs) = A.MaxEv $ M.fromList $ zip [q | BodyItem _ q _ _ _ <- bs] (repeat 1)
            
hoaToDPA :: HOA 
    -> Either [AccName] (A.DPA A.State (Maybe LabelExpr) (Maybe LabelExpr))
hoaToDPA h@(HOA hs bs) = 
   let  aps = concat [aps | AP aps <- hs]
        qs = hoaToStates bs
        ts = hoaToLabeledEdges (length aps) bs
        ss = hoaToStartStates hs
        [accn] = [ accn | AcceptanceName accn <- hs ]
   in case accn of
        Parity mm eo i -> Right 
            (A.makeAutomat qs ts ss (paracc mm eo i h)) 
            { A.aps = Just $ aps } 
        Buchi -> Right 
            (A.makeAutomat qs ts ss (buchitoparity qs h)) 
            { A.aps = Just $ aps } 
        Rabin 1 -> Right 
            (A.makeAutomat qs ts ss (rabin1toparity h)) 
            { A.aps = Just $ aps } 
        All -> Right 
            (A.makeAutomat qs ts ss (alltoparity h)) 
            { A.aps = Just $ aps } 
        None -> Right 
            (A.makeAutomat qs ts ss (nonetoparity h)) 
            { A.aps = Just $ aps } 
        _ -> Left [acc | AcceptanceName acc <- hs]
             
formToRab :: HoaAccCond -> [(Int, Int)]
formToRab (AccBoolExpr False) = []
formToRab (AccAnd (FinCond i) (InfCond j)) = [(i,j)]
formToRab (AccOr l r) = formToRab l ++ formToRab r

bitvOfLength :: Int -> [[LabelExpr -> LabelExpr]]
bitvOfLength naps = 
    reverse <$> (sequence $ replicate naps [LNot, id])
    
apInFormula :: Int -> LabelExpr -> Bool
apInFormula ap (RefAP i) = ap == i
apInFormula _ (LBoolExpr _) = False
apInFormula ap (LNot expr) = apInFormula ap expr
apInFormula ap (LAnd ex1 ex2) = apInFormula ap ex1 || apInFormula ap ex2
apInFormula ap (LOr ex1 ex2) = apInFormula ap ex1 || apInFormula ap ex2

    
expandFormula :: Int -> LabelExpr -> [LabelExpr]
expandFormula naps (LBoolExpr True) = do
    fs <- bitvOfLength naps
    return $ foldl1 LAnd
                $ zipWith ( \f i -> f $ RefAP i ) fs [0..]
    
expandFormula naps f = do
    let unfix = filter (\i -> not $ apInFormula i f) [0..naps-1]
    fs <- bitvOfLength $ length unfix
    let expr = foldl' LAnd f
                $ zipWith ( \f i -> f $ RefAP i ) fs unfix
    return expr
    
expandEdges :: Int ->  A.State ->  [EdgeItem]
            -> [(A.State, Maybe LabelExpr, A.State)]
expandEdges naps q es | all (isJust . edgeLabel) es  = do
    e <- es
    fs <- return $ edgeLabel e  
    q' <- stateConj e
    return (q, fs, q')
expandEdges naps q es | all (isNothing . edgeLabel) es  = do
        (e,fs) <- zip es $ bitvOfLength naps
        q' <- stateConj e
        let exp = foldl1 LAnd
                $ zipWith ( \f i -> f $ RefAP i ) fs [0..]
        return (q, Just exp, q')
  

hoaToLabeledEdges :: Int -> [BodyItem]
                  -> [(A.State, Maybe LabelExpr, A.State)]
hoaToLabeledEdges 0 bs = do
    BodyItem _ q _ _ es <- bs
    EdgeItem _ sc _ <- es
    q' <- sc
    return (q, Just $ LBoolExpr True , q')
    
hoaToLabeledEdges naps bs =
  bs >>= \b -> expandEdges naps (num b) (edges b)

hoaToDRA :: HOA 
         -> A.DRA A.State (Maybe LabelExpr) (Maybe LabelExpr)
hoaToDRA (HOA hs bs) =
  let aps = concat [aps | AP aps <- hs]
      qs = hoaToStates bs
      ts = hoaToLabeledEdges (length aps) bs
      ss = hoaToStartStates hs
      smap = M.fromListWith S.union $ do
          BodyItem _ q _ (Just is) _ <- bs
          i <- is
          return (i, S.singleton q)
      [f] = [f | Acceptance (_, f) <- hs]
      acc = map (\(i,j) -> (fromMaybe S.empty $ M.lookup i smap, fromMaybe S.empty $ M.lookup j smap)) $ formToRab f 
  in
      (A.makeAutomat qs ts ss acc) { A.aps = Just aps }



parseBodyItem :: Int -> [AliasName] -> Parser BodyItem
parseBodyItem i as = do
  parseAttribute "State"
  l <- option Nothing $ Just <$> brackets (parseLabelExpr i as)
  n <- decimal
  d <- option Nothing $ Just <$> parseDoubleQuotedString
  a <- option Nothing $ Just <$> parseAccSig
  es <- many $ parseEdgeItem i as
  return BodyItem
         { stateLabel = l
         , num = n
         , descr = d
         , stateAccSig = a
         , edges = es
         }


parseEdgeItem :: Int -> [AliasName] -> Parser EdgeItem
parseEdgeItem i as = do
  l <- option Nothing $ Just <$> brackets (parseLabelExpr i as)
  s <- parseConjunction decimal
  a <- option Nothing $ Just <$> parseAccSig
  return EdgeItem
         { edgeLabel = l
         , stateConj = s
         , accSig = a
         }


parseAccSig :: Parser [Int]
parseAccSig = curls $ many decimal


parseAttribute :: T.Text -> Parser ()
parseAttribute a = do
  token a
  token ":"
  return ()


parseProperties :: Parser HeaderItem
parseProperties = do
  parseAttribute "properties"
  Properties <$> many parseIdentifier <* whitespace


parseHeaderItem :: SM.StateT (Int, [AliasName]) Parser HeaderItem
parseHeaderItem = do
  (i, as) <- get
  r <- choice $ lift <$> [parseAccName,
                          parseAP,
                          parseStart,
                          parseNumStates,
                          parseHoaAccCond,
                          parseProperties,
                          parseTool,
                          parseName,
                          parseAlias i as]
  case r of
    (Alias (s, _)) -> put (i, s:as) >> return r
    (AP p) -> put (length p, as) >> return r
    _ -> return r


parseNumStates :: Parser HeaderItem
parseNumStates = do
  parseAttribute "States"
  num_states <- decimal
  return (NumStates num_states)


parseName :: Parser HeaderItem
parseName = do
  parseAttribute "name"
  Name <$> parseDoubleQuotedString


parseStart :: Parser HeaderItem
parseStart = do
  parseAttribute "Start"
  Start <$> decimal `sepBy1` token "&"


parseTool :: Parser HeaderItem
parseTool = do
  parseAttribute "tool"
  Tool <$> many parseDoubleQuotedString


parseAliasName :: Parser AliasName
parseAliasName = char '@' *> parseIdentifier <* whitespace


parseAlias :: Int -> [AliasName] -> Parser HeaderItem
parseAlias i as = do
  parseAttribute "Alias"
  a <- parseAliasName
  guard (not (a `elem` as)) <?> "Duplicate definition of aliases."
  expr <- parseLabelExpr i as
  return $ Alias (a, expr)


parseRefAlias :: [AliasName] -> Parser AliasName
parseRefAlias as = do
  a <- parseAliasName
  guard (a `elem` as) <?> "Reference to undefined alias name."
  return a


parseAccName :: Parser HeaderItem
parseAccName = do
  parseAttribute "acc-name"
  (AcceptanceName <$>
   ((token "Buchi" >> return Buchi) <|>
   (token "co-Buchi" >> return CoBuchi) <|>
   (token "all" >> return All) <|>
   (token "none" >> return None) <|>
   (GBuchi <$> (token "generalized-Buchi" >> decimal)) <|>
   (GCoBuchi <$> (token "generalized-co-Buchi" >> decimal)) <|>
   (Streett <$> (token "Streett" >> decimal)) <|>
   (Rabin <$> (token "Rabin" >> decimal)) <|>
   parseParityName <|>
   parseGRabinName))


parseParityName :: Parser AccName
parseParityName = do
  token "parity"
  skipSpace
  min_max <- (token "min" >> return Min) <|>
             (token "max" >> return Max)
  skipSpace
  even_odd <- (token "even" >> return Even) <|>
              (token "odd" >> return Odd)
  skipSpace
  n <- decimal
  return (Parity min_max even_odd n)


parseGRabinName :: Parser AccName
parseGRabinName = do
  token "generalized-Rabin"
  skipSpace
  n <- decimal
  nums <- count n decimal
  return $ GRabin n nums


parseLabelExpr :: Int -> [AliasName] -> Parser LabelExpr
parseLabelExpr i as = parseMBoolExpr p boolOps where
  p = RefAP <$> parseIntInRange i <|>
      RefAlias <$> parseRefAlias as


parseHoaAccCond :: Parser HeaderItem
parseHoaAccCond = do
  parseAttribute "Acceptance"
  i <- decimal
  acc <- parseAccCond i
  return (Acceptance (i, acc)) where
    parseAccCond i = parseMBoolExpr (p i) monotonicBoolOps
    p i = parseFin i <|>
          parseInf i <|>
          parseCompFin i<|>
          parseCompInf i
    parseAcc str p' = (token str) >> parens p'
    parseFin i = parseAcc "Fin" (FinCond <$> parseIntInRange i)
    parseInf i = parseAcc "Inf" (InfCond <$> parseIntInRange i)
    parseCompFin i = parseAcc "Fin" (token "!" >> (CompFinCond <$> parseIntInRange i))
    parseCompInf i = parseAcc "Inf" (token "!" >> (CompInfCond <$> parseIntInRange i))


parseAP :: Parser HeaderItem
parseAP = do
  parseAttribute "AP"
  num_aps <- decimal
  aps <- count num_aps (skipSpace >> parseDoubleQuotedString)
  return (AP aps)


parseIdentifier :: Parser T.Text
parseIdentifier = takeWhile1 (inClass "0-9a-zA-Z_-") <* (DAT.takeWhile (inClass " \t"))


-- | replace with "many1"
-- parseSpaceSeparated :: Parser a -> Parser [a]
-- parseSpaceSeparated p = p `sepBy1` many (DAT.string " ")


parseConjunction :: Parser a -> Parser [a]
parseConjunction p = p `sepBy1` (token "&")


monotonicBoolOps :: MBoolExpr a => [[Operator T.Text a]]
monotonicBoolOps = [[Infix ((token "&") >> return _and) AssocLeft]
                   ,[Infix ((token "|") >> return _or) AssocLeft]
                   ]


boolOps :: BoolExpr a => [[Operator T.Text a]]
boolOps = [[Prefix ((token "!") >> return _not)]] ++ monotonicBoolOps


parseMBoolExpr :: (MBoolExpr a) => Parser a -> [[Operator T.Text a]] -> Parser a
parseMBoolExpr p ops = buildExpressionParser ops term where
  term = ((token "t") >> return _true) <|>
         ((token "f") >> return _false) <|>
         parens (parseMBoolExpr p ops) <|>
         p

-- | Convert NBA into HOA format
nbaToHoa :: (Show q, Show l, Ord q)
   => A.NBA q (Maybe LabelExpr) l
   -> HOA
nbaToHoa a = let
  hs = [ NumStates $ S.size (A.states a)
       , Acceptance (1, InfCond 0)
       , Start $ [(A.toNode a q) - 1 | q <- S.toList (A.start a)]
       , Tool ["ldba-tool"]
       , AcceptanceName Buchi
       , AP $ fromJust $  A.aps a
       ]
  bs = [BodyItem{ stateLabel = Nothing
                , num = (A.toNode a q) - 1
                , descr = Nothing
                , stateAccSig = (if isAcc then Just [0] else Nothing)
                , edges = [EdgeItem{ edgeLabel = l
                                   , stateConj = [(A.toNode a q') - 1]
                                   , accSig = Nothing
                                   } | (q', l) <- A.succs a q]
                }
         | q <- S.toList (A.states a), let isAcc = S.member q (A.accept a)]
  in HOA hs bs

-- ACHTUNG: verschieden für maxev , minodd, ...
buildDPAacceptance :: A.ParityAccept q -> Int -> HoaAccCond
buildDPAacceptance acc nr =
    let fininfs = zipWith ($) (concat $ repeat [FinCond,InfCond]) [0..nr]
        inffins = zipWith ($) (concat $ repeat [InfCond,FinCond]) [0..nr]
    in case acc of
            A.MaxEv m -> buildmax AccAnd AccOr (head inffins) (tail inffins)
            A.MaxOdd m -> buildmax AccOr AccAnd (head fininfs) (tail fininfs)
            A.MinEv m -> buildmin AccOr AccAnd (head inffins) (tail inffins)
            A.MinOdd m -> buildmin AccAnd AccOr (head fininfs) (tail fininfs)
  
buildmin :: (HoaAccCond -> HoaAccCond -> HoaAccCond ) 
    -> (HoaAccCond -> HoaAccCond -> HoaAccCond ) 
    -> HoaAccCond -> [HoaAccCond] -> HoaAccCond
buildmin _ _ x [] = x
buildmin op1 _ x [y] = op1 x y
buildmin op1 op2 x (y:z:zs) = op1 x $ op2 y $ buildmin op1 op2 z zs
  
buildmax :: (HoaAccCond -> HoaAccCond -> HoaAccCond ) 
    -> (HoaAccCond -> HoaAccCond -> HoaAccCond ) 
    -> HoaAccCond -> [HoaAccCond] -> HoaAccCond
buildmax _ _ x [] = x
buildmax op1 _ x [y] = op1 x y
buildmax op1 op2 x (y:z:zs) = buildmax op1 op2 ( op2 (op1 x y) z) zs

  
tomapmaxpar :: A.ParityAccept q -> (M.Map q Int , Int) 
tomapmaxpar ac = case ac of
                 A.MaxEv m -> (m, maximum $ M.elems m)
                 A.MaxOdd m -> (m, maximum $ M.elems m)
                 A.MinEv m -> (m, maximum $ M.elems m)
                 A.MinOdd m -> (m, maximum $ M.elems m)
  
toaccname :: A.ParityAccept q -> AccName
toaccname pac = case pac of
                 A.MaxEv m -> Parity Max Even $ 1 + (maximum $ M.elems m)
                 A.MaxOdd m -> Parity Max Odd $ 1 + (maximum $ M.elems m)
                 A.MinEv m -> Parity Min Even $ 1 + (maximum $ M.elems m)
                 A.MinOdd m -> Parity Min Odd $ 1 + (maximum $ M.elems m)
      
  
dpaToHoa :: (Show q, Show l, Ord q) => A.DPA q (Maybe LabelExpr) l
                                    -> HOA
dpaToHoa a = 
    let (parmap, maxp) = tomapmaxpar $ A.accept a  
        hs = [ NumStates $ S.size (A.states a)
             , Start $ [(A.toNode a q) - 1 | q <- S.toList (A.start a)]
             , Tool ["optimized IAR", "v1"]
             , AcceptanceName $ toaccname $ A.accept a
             , Acceptance ( maxp + 1, buildDPAacceptance (A.accept a) maxp)
             , AP $ fromJust $  A.aps a
             ]
        bs = [BodyItem{ stateLabel = Nothing
                , num = (A.toNode a q) - 1
                , descr = Nothing
                , stateAccSig = case M.lookup q parmap of
                                     Just p -> Just [p]
                                     Nothing -> Nothing
                , edges = [EdgeItem{ edgeLabel = l
                                   , stateConj = [(A.toNode a q') - 1]
                                   , accSig = Nothing
                                   } | (q', l) <- A.succs a q]
                }
         | q <- S.toList (A.states a)]
    in HOA hs bs
  

buildDRAacceptance :: Int -> HeaderItem
buildDRAacceptance 0 = Acceptance (0, AccBoolExpr False)
buildDRAacceptance 1 = Acceptance (2, AccAnd (FinCond 0) (InfCond 1))
buildDRAacceptance n = 
    let Acceptance (_, accpre) = buildDRAacceptance (n-1)
    in Acceptance (2*n, AccOr accpre $ AccAnd (FinCond $ 2*(n-1)) (InfCond $ 2*(n-1)+1) )
  
inacc :: Ord q => q -> [A.Rabinpair q] -> Maybe [Int]
inacc q ps = 
    let qinpi i = 
            if even i 
               then S.member q $ fst $ ps !! (i `div` 2) 
               else S.member q $ snd $ ps !! (i `div` 2)
    in case filter qinpi [0 .. 2*(length ps)-1] of
         [] -> Nothing
         is -> Just is
  
draToHoa :: (Show q, Show l, Ord q) => A.DRA q (Maybe LabelExpr) l
                                    -> HOA
draToHoa a =
    let pairs = A.accept a
        -- maxpar = maximum $ M.elems parmap 
        hs = [ NumStates $ S.size (A.states a)
            , Start $ [(A.toNode a q) - 1 | q <- S.toList (A.start a)]
            , Tool ["optimized IAR", "v1"]
            , AcceptanceName $ Rabin $ length pairs
            , buildDRAacceptance $ length pairs
            , AP $ fromJust $  A.aps a
            ]
        bs = [BodyItem{ stateLabel = Nothing
                , num = (A.toNode a q) - 1
                , descr = Nothing
                , stateAccSig = inacc q pairs --  Just [parmap M.! q] 
                , edges = [EdgeItem{ edgeLabel = l
                                , stateConj = [(A.toNode a q') - 1]
                                , accSig = Nothing
                                } | (q', l) <- A.succs a q]
                }
            | q <- S.toList (A.states a)]
    in HOA hs bs
  
-- | Pretty-print Hoa Format
toHoa :: HOA -> String
toHoa (HOA hs bs) = unlines $ ["HOA: v1"] ++
                            (headerItemToHoa <$> hs) ++
                            ["--BODY--"] ++
                            [concat (bodyItemToHoa <$> bs) ++ "--END--"]


headerItemToHoa :: HeaderItem -> String
headerItemToHoa (NumStates i) = "States: " ++ show i
headerItemToHoa (AP as) = "AP: " ++ show (length as) ++
                          " " ++ unwords ((inDoubleQuotes . T.unpack) <$> as)
headerItemToHoa (Alias (n,l)) = "Alias: @" ++ T.unpack n ++ " " ++ labelExprToHoa l
headerItemToHoa (Acceptance (i, a)) = "Acceptance: " ++ show i ++ " " ++ accCondToHoa a
headerItemToHoa (Start ss) = "Start: " ++ concat  (intersperse "&" (show <$> ss))
headerItemToHoa (Tool ts) = "tool: " ++ unwords (map inDoubleQuotes (T.unpack <$> ts))
headerItemToHoa (Name s) = "name: " ++ inDoubleQuotes (T.unpack s)
headerItemToHoa (Properties ps) = "properties: " ++ unwords (T.unpack <$> ps)
headerItemToHoa (AcceptanceName n) = "acc-name: " ++ accNameToHoa n


accNameToHoa :: AccName -> String
accNameToHoa a = case a of
  Buchi -> "Buchi"
  CoBuchi -> "coBuchi"
  All -> "all"
  None -> "none"
  (GBuchi i) -> "generalized-Buchi " ++ show i
  (GCoBuchi i) -> "generalized-co-Buchi " ++ show i
  (Streett i) -> "Streett " ++ show i
  (Rabin i) -> "Rabin " ++ show i
  (Parity as b i) -> "parity " ++ minMaxToHoa as ++ " " ++ evenOddToHoa b ++ " " ++ show i where
    minMaxToHoa Min = "min"
    minMaxToHoa Max = "max"
    evenOddToHoa Even = "even"
    evenOddToHoa Odd = "odd"
  (GRabin i is) -> "generalized-Rabin " ++ show i ++ " " ++ unwords (show <$> is)


accCondToHoa :: HoaAccCond -> String
accCondToHoa (FinCond i) = "Fin" ++ inParens (show i)
accCondToHoa (InfCond i) = "Inf" ++ inParens (show i)
accCondToHoa (CompFinCond i) = "Fin" ++ inParens ("!" ++ show i)
accCondToHoa (CompInfCond i) = "Inf" ++ inParens ("!" ++ show i)
accCondToHoa (AccAnd e1 e2) = inParens (accCondToHoa e1 ++ " & " ++ accCondToHoa e2)
accCondToHoa (AccOr e1 e2) = inParens (accCondToHoa e1 ++ " | " ++ accCondToHoa e2)
accCondToHoa (AccBoolExpr b) = if b then "t" else "f"


labelExprToHoa :: LabelExpr -> String
labelExprToHoa (LBoolExpr b) = if b then "t" else "f"
labelExprToHoa (RefAP i) = show i
labelExprToHoa (RefAlias s) = "@" ++ T.unpack s
labelExprToHoa (LNot e) = "!" ++ labelExprToHoa e
labelExprToHoa (LAnd e1 e2) = inParens (labelExprToHoa e1 ++ " & " ++ labelExprToHoa e2)
labelExprToHoa (LOr e1 e2) = inParens (labelExprToHoa e1 ++ " | " ++ labelExprToHoa e2)


bodyItemToHoa :: BodyItem -> String
bodyItemToHoa b = ("State: " ++
                   maybeBlank labelExprToHoa (stateLabel b) ++
                   show (num b) ++ " " ++
                   maybeBlank (inDoubleQuotes . T.unpack) (descr b) ++
                   maybeBlank (inCurls . unwords . map show) (stateAccSig b) ++ "\n" ++
                   unlines [maybeBlank (inBrackets . labelExprToHoa) (edgeLabel e) ++
                            " " ++
                            concat (intersperse "&" (show <$> stateConj e)) ++
                            " " ++
                            maybeBlank (inCurls . unwords . map show) (accSig e)
                            | e <- edges b])


embracedBy :: Parser a -> T.Text -> T.Text -> Parser a
embracedBy p s1 s2 = do
  token s1
  r <- p
  token s2
  return r


parens :: Parser a -> Parser a
parens p = embracedBy p "(" ")"


brackets :: Parser a -> Parser a
brackets p = embracedBy p "[" "]"


curls :: Parser a -> Parser a
curls p = embracedBy p "{" "}"


-- skipNonToken :: Parser a -> Parser a
-- skipNonToken p =  whitespace *> p

whitespace :: Parser ()
whitespace = do
  skipSpace
  void $ many $ do
    DAT.string "/*" *> manyTill anyChar (DAT.string "*/")
    skipSpace

parseDoubleQuotedString :: Parser T.Text
parseDoubleQuotedString = do
  char '"'
  x <- many (notChar '\"' <|> (char '\\' >> char '\"'))
  char '"'
  whitespace
  return $ T.pack x


parseIntInRange :: Int -> Parser Int
parseIntInRange i = do
  x <- decimal
  guard (x >= 0 && x < i) <?> "Reference out of range."
  return x

decimal :: Parser Int
decimal = DAT.decimal <* whitespace 

token :: T.Text -> Parser ()
token s = DAT.string s *> whitespace


maybeBlank :: (a -> String) -> Maybe a -> String
maybeBlank _ Nothing = " "
maybeBlank f (Just a) = f a


inDoubleQuotes :: String -> String
inDoubleQuotes s = "\"" ++ s ++ "\""


inCurls :: String -> String
inCurls s = "{" ++ s ++ "}"


inParens :: String -> String
inParens s = "(" ++ s ++ ")"


inBrackets :: String -> String
inBrackets s = "[" ++ s ++ "]"
