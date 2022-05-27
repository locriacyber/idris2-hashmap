||| Internal functions used by HashMap and HashSet
module Data.HashMap.Internal

import Data.Array16
import Data.Fin
import Data.Bits
import public Data.Hashable

infix 6 `eq`

||| Mask for 4 bits.
export
BitMask : Type
BitMask = Fin 0x10

||| Initial bit mask.
export
bitMask0 : BitMask
bitMask0 = 0

public export
Hash : Type
Hash = Bits64

||| Mask 4 bits.
bitMask : BitMask -> Hash -> Bits64
bitMask mask h =        
    let mask_shift = weakenN 0x30 (mask * 4) in
    ((0x000000000000000f `shiftL` mask_shift) .&. h) `shiftR` mask_shift

||| Get the `BitMask` for the next 4 bits.
nextBitMask : BitMask -> BitMask
nextBitMask x = x + 1

||| Is this the last 4 bits?
isLastBM : BitMask -> Bool
isLastBM 0xf = True
isLastBM _   = False

public export
Salt : Type
Salt = Bits64

||| Get the next salt.
-- TODO: get better algorithm
nextSalt : Salt -> Salt
nextSalt = (2 +)

||| Return just if a predicate is satisfied.
justWhen : Bool -> Lazy a -> Maybe a
justWhen True x = Just x
justWhen False _ = Nothing

||| Return `Nothing` is predicate is false, else return other value.
joinWhen : Bool -> Lazy (Maybe a) -> Maybe a
joinWhen True x = x
joinWhen False _ = Nothing

||| Internal Hash-array map trie (HAMT) that assumes the same hash and Eq is used.
export
data HashArrayMapTrie k v
    = Empty
    | Leaf Hash k v -- full hash
    | Collision Hash Salt (HashArrayMapTrie k v) -- full hash
    | Node (Array16 (HashArrayMapTrie k v))

export
Functor (HashArrayMapTrie k) where
    map _ Empty = Empty
    map f (Leaf h k v) = Leaf h k (f v)
    map f (Collision h s m) = Collision h s (map f m)
    map f (Node arr) = Node (map (map f) arr)

||| An empty HAMT.
export
empty : HashArrayMapTrie k v
empty = Empty

||| A HAMT containing one key and value.
export
singleton : Hash -> k -> v -> HashArrayMapTrie k v
singleton = Leaf

||| Create a HAMT from 2 keys and values, which have different hashes.
node2 : BitMask -> Hash -> k -> v -> Hash -> k -> v -> HashArrayMapTrie k v
node2 bm h0 k0 v0 h1 k1 v1 = Node $
    write (bitMask bm h0) (Leaf h0 k0 v0) $
    write (bitMask bm h1) (Leaf h1 k1 v1) $
    new Empty

mutual
    ||| Create a HAMT from 2 keys and values, where the hashes collide.
    collision2 : 
        (eq : k -> k -> Bool) ->
        (hashWithSalt : Salt -> k -> Hash) ->
        Salt -> Hash ->
        k -> v -> k -> v ->
        HashArrayMapTrie k v
    collision2 eq hws s0 h k0 v0 k1 v1 =
        let s1 = nextSalt s0
            h0 = hws s1 k0
            h1 = hws s1 k1
            m0 = insert eq hws s1 bitMask0 h0 k0 v0
                $ insert eq hws s1 bitMask0 h1 k1 v1
                Empty
        in Collision h s1 m0

    export
    ||| Insert a key and value into a HAMT, replacing any existing values.
    insert :
        (eq : k -> k -> Bool) ->
        (hashWithSalt : Salt -> k -> Hash) ->
        Salt ->
        BitMask ->
        Hash ->
        k ->
        v ->
        HashArrayMapTrie k v ->
        HashArrayMapTrie k v
    insert eq hws s0 bitMask0 h0 k0 v0 m0 = case m0 of
        Empty => Leaf h0 k0 v0
        Leaf h1 k1 v1 => if h0 /= h1
            then node2 bitMask0 h0 k0 v0 h1 k1 v1
            else if k0 `eq` k1
                then Leaf h0 k0 v0
                else collision2 eq hws s0 h0 k0 v0 k1 v1
        Collision h1 s1 m1 => if h0 == h1
            then Collision h1 s1
                $ insert eq hws s1 bitMask0 (hws s1 k0) k0 v0 m1
            else -- hashes are different so it can't be the last bit mask
                Node $
                update (bitMask bitMask0 h0) (insert eq hws s0 (nextBitMask bitMask0) h0 k0 v0) $
                write (bitMask bitMask0 h1) m0 $
                new Empty
        Node ar =>
            Node $ update (bitMask bitMask0 h0)
            (insert eq hws s0 (nextBitMask bitMask0) h0 k0 v0) ar

||| Delete a key and value from a HAMT.
export
delete :
    (eq : k -> k -> Bool) ->
    (hashWithSalt : Salt -> k -> Hash) ->
    BitMask ->
    Hash -> k ->
    HashArrayMapTrie k v ->
    HashArrayMapTrie k v
delete eq hws bitMask0 h0 k0 m0 = case m0 of
    Empty => Empty
    Leaf h1 k1 v1 => if h0 == h1 && k0 `eq` k1
        then Empty
        else Leaf h1 k1 v1
    Collision h1 s1 m1 => if h0 == h1
        then Collision h1 s1
            $ delete eq hws bitMask0 (hws s1 k0) k0 m1
        else m0
    Node ar => Node $ update (bitMask bitMask0 h0) (delete eq hws (nextBitMask bitMask0) h0 k0) ar

||| Lookup a value at a key in a HAMT.
export
lookup :
    (eq : k -> k -> Bool) ->
    (hashWithSalt : Salt -> k -> Hash) ->
    BitMask ->
    Hash -> k ->
    HashArrayMapTrie k v ->
    Maybe v
lookup eq hws bitMask0 h0 k0 m0 = case m0 of
    Empty => Nothing
    Leaf h1 k1 v => justWhen (h0 == h1 && k0 `eq` k1) v
    Collision h1 s m1 => joinWhen (h0 == h1)
        $ lookup eq hws bitMask0 (hws s k0) k0 m1
    Node ar => lookup eq hws (nextBitMask bitMask0) h0 k0 $ index (bitMask bitMask0 h0) ar

||| Fold a HAMT with the key and value.
||| Note: this is based on the order of the hash not the key.
export
foldWithKey : (k -> v -> acc -> acc) -> acc -> HashArrayMapTrie k v -> acc
foldWithKey _ z Empty = z
foldWithKey f z (Leaf _ k v) = f k v z
foldWithKey f z (Collision _ _ m) = foldWithKey f z m
foldWithKey f z (Node ar) = foldr (flip $ foldWithKey f) z ar
