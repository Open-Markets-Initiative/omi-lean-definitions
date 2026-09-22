import Omi.Wire

/-!
# Australian Securities Exchange Asx Trade v2.0

Generated from the binary model, with the proofs the model's rules call for: every record
decodes back to what was encoded; a message dispatch selects the message its type names;
a count is written from the list it counts; a length prefix is written from the bytes it frames;
and a packet read to the end of its data decodes to the messages that were written.

Note: a Message Count of 0 marks Heartbeat and carries no messages; the decoder reads it as a count and the encoder never writes it.

Note: a Message Count of 65535 marks End Of Session and carries no messages; the decoder reads it as a count and the encoder never writes it.

Note: Exchange Order Type is a bit field set, proven as its 2 byte integer rather than bit by bit.

Text fields are kept byte for byte, padding included, so what is decoded encodes back unchanged.
Prices with implied decimals are proven as the integers on the wire.
-/

namespace Omi.AsxAsxsecuritiesTradeItchV20

/-- Leg 1 Side: one byte code -/
def Leg1Side.codes : List UInt8 :=
  [0x42, 0x43]

inductive Leg1Side where
  | buyLeg -- Buy Leg
  | sellLeg -- Sell Leg
  | unlisted (byte : { byte : UInt8 // byte ∉ Leg1Side.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace Leg1Side

def toByte : Leg1Side → UInt8
  | .buyLeg => 0x42
  | .sellLeg => 0x43
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : Leg1Side :=
  if byte = 0x42 then .buyLeg
  else .sellLeg

def ofByte (byte : UInt8) : Leg1Side :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : Leg1Side) : ofByte value.toByte = value := by
  cases value with
  | buyLeg => decide
  | sellLeg => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : Leg1Side) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (Leg1Side × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : Leg1Side) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : Leg1Side) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end Leg1Side

/-- Leg 2 Side: one byte code -/
def Leg2Side.codes : List UInt8 :=
  [0x42, 0x43]

inductive Leg2Side where
  | buyLeg -- Buy Leg
  | sellLeg -- Sell Leg
  | unlisted (byte : { byte : UInt8 // byte ∉ Leg2Side.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace Leg2Side

def toByte : Leg2Side → UInt8
  | .buyLeg => 0x42
  | .sellLeg => 0x43
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : Leg2Side :=
  if byte = 0x42 then .buyLeg
  else .sellLeg

def ofByte (byte : UInt8) : Leg2Side :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : Leg2Side) : ofByte value.toByte = value := by
  cases value with
  | buyLeg => decide
  | sellLeg => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : Leg2Side) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (Leg2Side × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : Leg2Side) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : Leg2Side) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end Leg2Side

/-- Leg 3 Side: one byte code -/
def Leg3Side.codes : List UInt8 :=
  [0x42, 0x43, 0x3F]

inductive Leg3Side where
  | buyLeg -- Buy Leg
  | sellLeg -- Sell Leg
  | notDefined -- Not Defined
  | unlisted (byte : { byte : UInt8 // byte ∉ Leg3Side.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace Leg3Side

def toByte : Leg3Side → UInt8
  | .buyLeg => 0x42
  | .sellLeg => 0x43
  | .notDefined => 0x3F
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : Leg3Side :=
  if byte = 0x42 then .buyLeg
  else if byte = 0x43 then .sellLeg
  else .notDefined

def ofByte (byte : UInt8) : Leg3Side :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : Leg3Side) : ofByte value.toByte = value := by
  cases value with
  | buyLeg => decide
  | sellLeg => decide
  | notDefined => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : Leg3Side) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (Leg3Side × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : Leg3Side) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : Leg3Side) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end Leg3Side

/-- Leg 4 Side: one byte code -/
def Leg4Side.codes : List UInt8 :=
  [0x42, 0x43, 0x3F]

inductive Leg4Side where
  | buyLeg -- Buy Leg
  | sellLeg -- Sell Leg
  | notDefined -- Not Defined
  | unlisted (byte : { byte : UInt8 // byte ∉ Leg4Side.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace Leg4Side

def toByte : Leg4Side → UInt8
  | .buyLeg => 0x42
  | .sellLeg => 0x43
  | .notDefined => 0x3F
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : Leg4Side :=
  if byte = 0x42 then .buyLeg
  else if byte = 0x43 then .sellLeg
  else .notDefined

def ofByte (byte : UInt8) : Leg4Side :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : Leg4Side) : ofByte value.toByte = value := by
  cases value with
  | buyLeg => decide
  | sellLeg => decide
  | notDefined => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : Leg4Side) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (Leg4Side × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : Leg4Side) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : Leg4Side) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end Leg4Side

/-- Event Code: one byte code -/
def EventCode.codes : List UInt8 :=
  [0x4F, 0x43]

inductive EventCode where
  | startOfMessages -- Start Of Messages
  | endOfMessages -- End Of Messages
  | unlisted (byte : { byte : UInt8 // byte ∉ EventCode.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace EventCode

def toByte : EventCode → UInt8
  | .startOfMessages => 0x4F
  | .endOfMessages => 0x43
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : EventCode :=
  if byte = 0x4F then .startOfMessages
  else .endOfMessages

def ofByte (byte : UInt8) : EventCode :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : EventCode) : ofByte value.toByte = value := by
  cases value with
  | startOfMessages => decide
  | endOfMessages => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : EventCode) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (EventCode × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : EventCode) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : EventCode) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end EventCode

/-- Side: one byte code -/
def Side.codes : List UInt8 :=
  [0x53, 0x42]

inductive Side where
  | sell -- Sell
  | buy -- Buy
  | unlisted (byte : { byte : UInt8 // byte ∉ Side.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace Side

def toByte : Side → UInt8
  | .sell => 0x53
  | .buy => 0x42
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : Side :=
  if byte = 0x53 then .sell
  else .buy

def ofByte (byte : UInt8) : Side :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : Side) : ofByte value.toByte = value := by
  cases value with
  | sell => decide
  | buy => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : Side) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (Side × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : Side) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : Side) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end Side

/-- Occurred At Cross: one byte code -/
def OccurredAtCross.codes : List UInt8 :=
  [0x59, 0x4E]

inductive OccurredAtCross where
  | yes -- Yes
  | no -- No
  | unlisted (byte : { byte : UInt8 // byte ∉ OccurredAtCross.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace OccurredAtCross

def toByte : OccurredAtCross → UInt8
  | .yes => 0x59
  | .no => 0x4E
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : OccurredAtCross :=
  if byte = 0x59 then .yes
  else .no

def ofByte (byte : UInt8) : OccurredAtCross :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : OccurredAtCross) : ofByte value.toByte = value := by
  cases value with
  | yes => decide
  | no => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : OccurredAtCross) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (OccurredAtCross × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : OccurredAtCross) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : OccurredAtCross) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end OccurredAtCross

/-- Printable: one byte code -/
def Printable.codes : List UInt8 :=
  [0x59, 0x4E]

inductive Printable where
  | yes -- Yes
  | no -- No
  | unlisted (byte : { byte : UInt8 // byte ∉ Printable.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace Printable

def toByte : Printable → UInt8
  | .yes => 0x59
  | .no => 0x4E
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : Printable :=
  if byte = 0x59 then .yes
  else .no

def ofByte (byte : UInt8) : Printable :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : Printable) : ofByte value.toByte = value := by
  cases value with
  | yes => decide
  | no => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : Printable) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (Printable × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : Printable) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : Printable) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end Printable

/-- Seconds Message: 4 bytes -/
structure SecondsMessage where
  second : BitVec 32
  deriving DecidableEq, Repr

namespace SecondsMessage

def encode (message : SecondsMessage) : List UInt8 :=
  encodeUInt 4 message.second

def decode (bytes : List UInt8) : Option (SecondsMessage × List UInt8) := do
  let (second, bytes) ← decodeUInt 4 bytes
  pure ({ second }, bytes)

@[simp] theorem encode_length (message : SecondsMessage) : (encode message).length = 4 := by
  unfold encode
  simp only [encodeUInt_length]

theorem encode_length_pos (message : SecondsMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SecondsMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end SecondsMessage

/-- Order Book Directory Message: 112 bytes -/
structure OrderBookDirectoryMessage where
  nanoseconds : BitVec 32
  orderBookId : BitVec 32
  symbol : Alpha 32
  longName : Alpha 32
  isin : Alpha 12
  financialProduct : BitVec 8
  tradingCurrency : Alpha 3
  numberOfDecimalsInPrice : BitVec 16
  numberOfDecimalsInNominalValue : BitVec 16
  oddLotSize : BitVec 32
  roundLotSize : BitVec 32
  blockLotSize : BitVec 32
  nominalValue : BitVec 64
  deriving DecidableEq, Repr

namespace OrderBookDirectoryMessage

def encode (message : OrderBookDirectoryMessage) : List UInt8 :=
  encodeUInt 4 message.nanoseconds
    ++ (encodeUInt 4 message.orderBookId
    ++ (Alpha.encode message.symbol
    ++ (Alpha.encode message.longName
    ++ (Alpha.encode message.isin
    ++ (encodeUInt 1 message.financialProduct
    ++ (Alpha.encode message.tradingCurrency
    ++ (encodeUInt 2 message.numberOfDecimalsInPrice
    ++ (encodeUInt 2 message.numberOfDecimalsInNominalValue
    ++ (encodeUInt 4 message.oddLotSize
    ++ (encodeUInt 4 message.roundLotSize
    ++ (encodeUInt 4 message.blockLotSize
    ++ (encodeUInt 8 message.nominalValue))))))))))))

def decode (bytes : List UInt8) : Option (OrderBookDirectoryMessage × List UInt8) := do
  let (nanoseconds, bytes) ← decodeUInt 4 bytes
  let (orderBookId, bytes) ← decodeUInt 4 bytes
  let (symbol, bytes) ← Alpha.decode 32 bytes
  let (longName, bytes) ← Alpha.decode 32 bytes
  let (isin, bytes) ← Alpha.decode 12 bytes
  let (financialProduct, bytes) ← decodeUInt 1 bytes
  let (tradingCurrency, bytes) ← Alpha.decode 3 bytes
  let (numberOfDecimalsInPrice, bytes) ← decodeUInt 2 bytes
  let (numberOfDecimalsInNominalValue, bytes) ← decodeUInt 2 bytes
  let (oddLotSize, bytes) ← decodeUInt 4 bytes
  let (roundLotSize, bytes) ← decodeUInt 4 bytes
  let (blockLotSize, bytes) ← decodeUInt 4 bytes
  let (nominalValue, bytes) ← decodeUInt 8 bytes
  pure ({ nanoseconds, orderBookId, symbol, longName, isin, financialProduct, tradingCurrency, numberOfDecimalsInPrice, numberOfDecimalsInNominalValue, oddLotSize, roundLotSize, blockLotSize, nominalValue }, bytes)

@[simp] theorem encode_length (message : OrderBookDirectoryMessage) : (encode message).length = 112 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Alpha.encode_length]

theorem encode_length_pos (message : OrderBookDirectoryMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OrderBookDirectoryMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end OrderBookDirectoryMessage

/-- Combination Order Book Directory Message: 260 bytes -/
structure CombinationOrderBookDirectoryMessage where
  nanoseconds : BitVec 32
  orderBookId : BitVec 32
  symbol : Alpha 32
  longName : Alpha 32
  isin : Alpha 12
  financialProduct : BitVec 8
  tradingCurrency : Alpha 3
  numberOfDecimalsInPrice : BitVec 16
  numberOfDecimalsInNominalValue : BitVec 16
  oddLotSize : BitVec 32
  roundLotSize : BitVec 32
  blockLotSize : BitVec 32
  nominalValue : BitVec 64
  leg1Symbol : Alpha 32
  leg1Side : Leg1Side
  leg1Ratio : BitVec 32
  leg2Symbol : Alpha 32
  leg2Side : Leg2Side
  leg2Ratio : BitVec 32
  leg3Symbol : Alpha 32
  leg3Side : Leg3Side
  leg3Ratio : BitVec 32
  leg4Symbol : Alpha 32
  leg4Side : Leg4Side
  leg4Ratio : BitVec 32
  deriving DecidableEq, Repr

namespace CombinationOrderBookDirectoryMessage

def encode (message : CombinationOrderBookDirectoryMessage) : List UInt8 :=
  encodeUInt 4 message.nanoseconds
    ++ (encodeUInt 4 message.orderBookId
    ++ (Alpha.encode message.symbol
    ++ (Alpha.encode message.longName
    ++ (Alpha.encode message.isin
    ++ (encodeUInt 1 message.financialProduct
    ++ (Alpha.encode message.tradingCurrency
    ++ (encodeUInt 2 message.numberOfDecimalsInPrice
    ++ (encodeUInt 2 message.numberOfDecimalsInNominalValue
    ++ (encodeUInt 4 message.oddLotSize
    ++ (encodeUInt 4 message.roundLotSize
    ++ (encodeUInt 4 message.blockLotSize
    ++ (encodeUInt 8 message.nominalValue
    ++ (Alpha.encode message.leg1Symbol
    ++ (Leg1Side.encode message.leg1Side
    ++ (encodeUInt 4 message.leg1Ratio
    ++ (Alpha.encode message.leg2Symbol
    ++ (Leg2Side.encode message.leg2Side
    ++ (encodeUInt 4 message.leg2Ratio
    ++ (Alpha.encode message.leg3Symbol
    ++ (Leg3Side.encode message.leg3Side
    ++ (encodeUInt 4 message.leg3Ratio
    ++ (Alpha.encode message.leg4Symbol
    ++ (Leg4Side.encode message.leg4Side
    ++ (encodeUInt 4 message.leg4Ratio))))))))))))))))))))))))

-- a long run of fields nests deeper than the elaborator's default limit
set_option maxRecDepth 4096 in
def decode (bytes : List UInt8) : Option (CombinationOrderBookDirectoryMessage × List UInt8) := do
  let (nanoseconds, bytes) ← decodeUInt 4 bytes
  let (orderBookId, bytes) ← decodeUInt 4 bytes
  let (symbol, bytes) ← Alpha.decode 32 bytes
  let (longName, bytes) ← Alpha.decode 32 bytes
  let (isin, bytes) ← Alpha.decode 12 bytes
  let (financialProduct, bytes) ← decodeUInt 1 bytes
  let (tradingCurrency, bytes) ← Alpha.decode 3 bytes
  let (numberOfDecimalsInPrice, bytes) ← decodeUInt 2 bytes
  let (numberOfDecimalsInNominalValue, bytes) ← decodeUInt 2 bytes
  let (oddLotSize, bytes) ← decodeUInt 4 bytes
  let (roundLotSize, bytes) ← decodeUInt 4 bytes
  let (blockLotSize, bytes) ← decodeUInt 4 bytes
  let (nominalValue, bytes) ← decodeUInt 8 bytes
  let (leg1Symbol, bytes) ← Alpha.decode 32 bytes
  let (leg1Side, bytes) ← Leg1Side.decode bytes
  let (leg1Ratio, bytes) ← decodeUInt 4 bytes
  let (leg2Symbol, bytes) ← Alpha.decode 32 bytes
  let (leg2Side, bytes) ← Leg2Side.decode bytes
  let (leg2Ratio, bytes) ← decodeUInt 4 bytes
  let (leg3Symbol, bytes) ← Alpha.decode 32 bytes
  let (leg3Side, bytes) ← Leg3Side.decode bytes
  let (leg3Ratio, bytes) ← decodeUInt 4 bytes
  let (leg4Symbol, bytes) ← Alpha.decode 32 bytes
  let (leg4Side, bytes) ← Leg4Side.decode bytes
  let (leg4Ratio, bytes) ← decodeUInt 4 bytes
  pure ({ nanoseconds, orderBookId, symbol, longName, isin, financialProduct, tradingCurrency, numberOfDecimalsInPrice, numberOfDecimalsInNominalValue, oddLotSize, roundLotSize, blockLotSize, nominalValue, leg1Symbol, leg1Side, leg1Ratio, leg2Symbol, leg2Side, leg2Ratio, leg3Symbol, leg3Side, leg3Ratio, leg4Symbol, leg4Side, leg4Ratio }, bytes)

@[simp] theorem encode_length (message : CombinationOrderBookDirectoryMessage) : (encode message).length = 260 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Alpha.encode_length, Leg1Side.encode_length, Leg2Side.encode_length, Leg3Side.encode_length, Leg4Side.encode_length]

theorem encode_length_pos (message : CombinationOrderBookDirectoryMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

set_option maxRecDepth 4096 in
@[simp] theorem decode_encode (message : CombinationOrderBookDirectoryMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Leg1Side.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Leg2Side.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Leg3Side.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Leg4Side.decode_encode, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end CombinationOrderBookDirectoryMessage

/-- Tick Size Message: 24 bytes -/
structure TickSizeMessage where
  nanoseconds : BitVec 32
  orderBookId : BitVec 32
  tickSize : BitVec 64
  priceFrom : BitVec 32
  priceTo : BitVec 32
  deriving DecidableEq, Repr

namespace TickSizeMessage

def encode (message : TickSizeMessage) : List UInt8 :=
  encodeUInt 4 message.nanoseconds
    ++ (encodeUInt 4 message.orderBookId
    ++ (encodeUInt 8 message.tickSize
    ++ (encodeUInt 4 message.priceFrom
    ++ (encodeUInt 4 message.priceTo))))

def decode (bytes : List UInt8) : Option (TickSizeMessage × List UInt8) := do
  let (nanoseconds, bytes) ← decodeUInt 4 bytes
  let (orderBookId, bytes) ← decodeUInt 4 bytes
  let (tickSize, bytes) ← decodeUInt 8 bytes
  let (priceFrom, bytes) ← decodeUInt 4 bytes
  let (priceTo, bytes) ← decodeUInt 4 bytes
  pure ({ nanoseconds, orderBookId, tickSize, priceFrom, priceTo }, bytes)

@[simp] theorem encode_length (message : TickSizeMessage) : (encode message).length = 24 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length]

theorem encode_length_pos (message : TickSizeMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : TickSizeMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end TickSizeMessage

/-- System Event Message: 5 bytes -/
structure SystemEventMessage where
  nanoseconds : BitVec 32
  eventCode : EventCode
  deriving DecidableEq, Repr

namespace SystemEventMessage

def encode (message : SystemEventMessage) : List UInt8 :=
  encodeUInt 4 message.nanoseconds
    ++ (EventCode.encode message.eventCode)

def decode (bytes : List UInt8) : Option (SystemEventMessage × List UInt8) := do
  let (nanoseconds, bytes) ← decodeUInt 4 bytes
  let (eventCode, bytes) ← EventCode.decode bytes
  pure ({ nanoseconds, eventCode }, bytes)

@[simp] theorem encode_length (message : SystemEventMessage) : (encode message).length = 5 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, EventCode.encode_length]

theorem encode_length_pos (message : SystemEventMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SystemEventMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [EventCode.decode_encode, some_bind]
  rfl

end SystemEventMessage

/-- Order Book State Message: 28 bytes -/
structure OrderBookStateMessage where
  nanoseconds : BitVec 32
  orderBookId : BitVec 32
  stateName : Alpha 20
  deriving DecidableEq, Repr

namespace OrderBookStateMessage

def encode (message : OrderBookStateMessage) : List UInt8 :=
  encodeUInt 4 message.nanoseconds
    ++ (encodeUInt 4 message.orderBookId
    ++ (Alpha.encode message.stateName))

def decode (bytes : List UInt8) : Option (OrderBookStateMessage × List UInt8) := do
  let (nanoseconds, bytes) ← decodeUInt 4 bytes
  let (orderBookId, bytes) ← decodeUInt 4 bytes
  let (stateName, bytes) ← Alpha.decode 20 bytes
  pure ({ nanoseconds, orderBookId, stateName }, bytes)

@[simp] theorem encode_length (message : OrderBookStateMessage) : (encode message).length = 28 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Alpha.encode_length]

theorem encode_length_pos (message : OrderBookStateMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OrderBookStateMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end OrderBookStateMessage

/-- Add Order No Participant Id Message: 36 bytes -/
structure AddOrderNoParticipantIdMessage where
  nanoseconds : BitVec 32
  orderId : BitVec 64
  orderBookId : BitVec 32
  side : Side
  orderBookPosition : BitVec 32
  quantity : BitVec 64
  price : BitVec 32
  exchangeOrderType : BitVec 16
  lotType : BitVec 8
  deriving DecidableEq, Repr

namespace AddOrderNoParticipantIdMessage

def encode (message : AddOrderNoParticipantIdMessage) : List UInt8 :=
  encodeUInt 4 message.nanoseconds
    ++ (encodeUInt 8 message.orderId
    ++ (encodeUInt 4 message.orderBookId
    ++ (Side.encode message.side
    ++ (encodeUInt 4 message.orderBookPosition
    ++ (encodeUInt 8 message.quantity
    ++ (encodeUInt 4 message.price
    ++ (encodeUInt 2 message.exchangeOrderType
    ++ (encodeUInt 1 message.lotType))))))))

def decode (bytes : List UInt8) : Option (AddOrderNoParticipantIdMessage × List UInt8) := do
  let (nanoseconds, bytes) ← decodeUInt 4 bytes
  let (orderId, bytes) ← decodeUInt 8 bytes
  let (orderBookId, bytes) ← decodeUInt 4 bytes
  let (side, bytes) ← Side.decode bytes
  let (orderBookPosition, bytes) ← decodeUInt 4 bytes
  let (quantity, bytes) ← decodeUInt 8 bytes
  let (price, bytes) ← decodeUInt 4 bytes
  let (exchangeOrderType, bytes) ← decodeUInt 2 bytes
  let (lotType, bytes) ← decodeUInt 1 bytes
  pure ({ nanoseconds, orderId, orderBookId, side, orderBookPosition, quantity, price, exchangeOrderType, lotType }, bytes)

@[simp] theorem encode_length (message : AddOrderNoParticipantIdMessage) : (encode message).length = 36 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Side.encode_length]

theorem encode_length_pos (message : AddOrderNoParticipantIdMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : AddOrderNoParticipantIdMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Side.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end AddOrderNoParticipantIdMessage

/-- Add Order Participant Id Message: 43 bytes -/
structure AddOrderParticipantIdMessage where
  nanoseconds : BitVec 32
  orderId : BitVec 64
  orderBookId : BitVec 32
  side : Side
  orderBookPosition : BitVec 32
  quantity : BitVec 64
  price : BitVec 32
  exchangeOrderType : BitVec 16
  lotType : BitVec 8
  participantId : Alpha 7
  deriving DecidableEq, Repr

namespace AddOrderParticipantIdMessage

def encode (message : AddOrderParticipantIdMessage) : List UInt8 :=
  encodeUInt 4 message.nanoseconds
    ++ (encodeUInt 8 message.orderId
    ++ (encodeUInt 4 message.orderBookId
    ++ (Side.encode message.side
    ++ (encodeUInt 4 message.orderBookPosition
    ++ (encodeUInt 8 message.quantity
    ++ (encodeUInt 4 message.price
    ++ (encodeUInt 2 message.exchangeOrderType
    ++ (encodeUInt 1 message.lotType
    ++ (Alpha.encode message.participantId)))))))))

def decode (bytes : List UInt8) : Option (AddOrderParticipantIdMessage × List UInt8) := do
  let (nanoseconds, bytes) ← decodeUInt 4 bytes
  let (orderId, bytes) ← decodeUInt 8 bytes
  let (orderBookId, bytes) ← decodeUInt 4 bytes
  let (side, bytes) ← Side.decode bytes
  let (orderBookPosition, bytes) ← decodeUInt 4 bytes
  let (quantity, bytes) ← decodeUInt 8 bytes
  let (price, bytes) ← decodeUInt 4 bytes
  let (exchangeOrderType, bytes) ← decodeUInt 2 bytes
  let (lotType, bytes) ← decodeUInt 1 bytes
  let (participantId, bytes) ← Alpha.decode 7 bytes
  pure ({ nanoseconds, orderId, orderBookId, side, orderBookPosition, quantity, price, exchangeOrderType, lotType, participantId }, bytes)

@[simp] theorem encode_length (message : AddOrderParticipantIdMessage) : (encode message).length = 43 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Side.encode_length, Alpha.encode_length]

theorem encode_length_pos (message : AddOrderParticipantIdMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : AddOrderParticipantIdMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Side.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end AddOrderParticipantIdMessage

/-- Order Executed Message: 51 bytes -/
structure OrderExecutedMessage where
  nanoseconds : BitVec 32
  orderId : BitVec 64
  orderBookId : BitVec 32
  side : Side
  executedQuantity : BitVec 64
  matchId : BitVec 96
  participantIdOwner : Alpha 7
  participantIdCounterparty : Alpha 7
  deriving DecidableEq, Repr

namespace OrderExecutedMessage

def encode (message : OrderExecutedMessage) : List UInt8 :=
  encodeUInt 4 message.nanoseconds
    ++ (encodeUInt 8 message.orderId
    ++ (encodeUInt 4 message.orderBookId
    ++ (Side.encode message.side
    ++ (encodeUInt 8 message.executedQuantity
    ++ (encodeUInt 12 message.matchId
    ++ (Alpha.encode message.participantIdOwner
    ++ (Alpha.encode message.participantIdCounterparty)))))))

def decode (bytes : List UInt8) : Option (OrderExecutedMessage × List UInt8) := do
  let (nanoseconds, bytes) ← decodeUInt 4 bytes
  let (orderId, bytes) ← decodeUInt 8 bytes
  let (orderBookId, bytes) ← decodeUInt 4 bytes
  let (side, bytes) ← Side.decode bytes
  let (executedQuantity, bytes) ← decodeUInt 8 bytes
  let (matchId, bytes) ← decodeUInt 12 bytes
  let (participantIdOwner, bytes) ← Alpha.decode 7 bytes
  let (participantIdCounterparty, bytes) ← Alpha.decode 7 bytes
  pure ({ nanoseconds, orderId, orderBookId, side, executedQuantity, matchId, participantIdOwner, participantIdCounterparty }, bytes)

@[simp] theorem encode_length (message : OrderExecutedMessage) : (encode message).length = 51 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Side.encode_length, Alpha.encode_length]

theorem encode_length_pos (message : OrderExecutedMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OrderExecutedMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Side.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end OrderExecutedMessage

/-- Order Executed With Price Message: 57 bytes -/
structure OrderExecutedWithPriceMessage where
  nanoseconds : BitVec 32
  orderId : BitVec 64
  orderBookId : BitVec 32
  side : Side
  executedQuantity : BitVec 64
  matchId : BitVec 96
  participantIdOwner : Alpha 7
  participantIdCounterparty : Alpha 7
  tradePrice : BitVec 32
  occurredAtCross : OccurredAtCross
  printable : Printable
  deriving DecidableEq, Repr

namespace OrderExecutedWithPriceMessage

def encode (message : OrderExecutedWithPriceMessage) : List UInt8 :=
  encodeUInt 4 message.nanoseconds
    ++ (encodeUInt 8 message.orderId
    ++ (encodeUInt 4 message.orderBookId
    ++ (Side.encode message.side
    ++ (encodeUInt 8 message.executedQuantity
    ++ (encodeUInt 12 message.matchId
    ++ (Alpha.encode message.participantIdOwner
    ++ (Alpha.encode message.participantIdCounterparty
    ++ (encodeUInt 4 message.tradePrice
    ++ (OccurredAtCross.encode message.occurredAtCross
    ++ (Printable.encode message.printable))))))))))

def decode (bytes : List UInt8) : Option (OrderExecutedWithPriceMessage × List UInt8) := do
  let (nanoseconds, bytes) ← decodeUInt 4 bytes
  let (orderId, bytes) ← decodeUInt 8 bytes
  let (orderBookId, bytes) ← decodeUInt 4 bytes
  let (side, bytes) ← Side.decode bytes
  let (executedQuantity, bytes) ← decodeUInt 8 bytes
  let (matchId, bytes) ← decodeUInt 12 bytes
  let (participantIdOwner, bytes) ← Alpha.decode 7 bytes
  let (participantIdCounterparty, bytes) ← Alpha.decode 7 bytes
  let (tradePrice, bytes) ← decodeUInt 4 bytes
  let (occurredAtCross, bytes) ← OccurredAtCross.decode bytes
  let (printable, bytes) ← Printable.decode bytes
  pure ({ nanoseconds, orderId, orderBookId, side, executedQuantity, matchId, participantIdOwner, participantIdCounterparty, tradePrice, occurredAtCross, printable }, bytes)

@[simp] theorem encode_length (message : OrderExecutedWithPriceMessage) : (encode message).length = 57 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Side.encode_length, Alpha.encode_length, OccurredAtCross.encode_length, Printable.encode_length]

theorem encode_length_pos (message : OrderExecutedWithPriceMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OrderExecutedWithPriceMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Side.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, OccurredAtCross.decode_encode, some_bind]
  dsimp only
  rw [Printable.decode_encode, some_bind]
  rfl

end OrderExecutedWithPriceMessage

/-- Order Replace Message: 35 bytes -/
structure OrderReplaceMessage where
  nanoseconds : BitVec 32
  orderId : BitVec 64
  orderBookId : BitVec 32
  side : Side
  newOrderBookPosition : BitVec 32
  quantity : BitVec 64
  price : BitVec 32
  exchangeOrderType : BitVec 16
  deriving DecidableEq, Repr

namespace OrderReplaceMessage

def encode (message : OrderReplaceMessage) : List UInt8 :=
  encodeUInt 4 message.nanoseconds
    ++ (encodeUInt 8 message.orderId
    ++ (encodeUInt 4 message.orderBookId
    ++ (Side.encode message.side
    ++ (encodeUInt 4 message.newOrderBookPosition
    ++ (encodeUInt 8 message.quantity
    ++ (encodeUInt 4 message.price
    ++ (encodeUInt 2 message.exchangeOrderType)))))))

def decode (bytes : List UInt8) : Option (OrderReplaceMessage × List UInt8) := do
  let (nanoseconds, bytes) ← decodeUInt 4 bytes
  let (orderId, bytes) ← decodeUInt 8 bytes
  let (orderBookId, bytes) ← decodeUInt 4 bytes
  let (side, bytes) ← Side.decode bytes
  let (newOrderBookPosition, bytes) ← decodeUInt 4 bytes
  let (quantity, bytes) ← decodeUInt 8 bytes
  let (price, bytes) ← decodeUInt 4 bytes
  let (exchangeOrderType, bytes) ← decodeUInt 2 bytes
  pure ({ nanoseconds, orderId, orderBookId, side, newOrderBookPosition, quantity, price, exchangeOrderType }, bytes)

@[simp] theorem encode_length (message : OrderReplaceMessage) : (encode message).length = 35 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Side.encode_length]

theorem encode_length_pos (message : OrderReplaceMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OrderReplaceMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Side.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end OrderReplaceMessage

/-- Order Delete Message: 17 bytes -/
structure OrderDeleteMessage where
  nanoseconds : BitVec 32
  orderId : BitVec 64
  orderBookId : BitVec 32
  side : Side
  deriving DecidableEq, Repr

namespace OrderDeleteMessage

def encode (message : OrderDeleteMessage) : List UInt8 :=
  encodeUInt 4 message.nanoseconds
    ++ (encodeUInt 8 message.orderId
    ++ (encodeUInt 4 message.orderBookId
    ++ (Side.encode message.side)))

def decode (bytes : List UInt8) : Option (OrderDeleteMessage × List UInt8) := do
  let (nanoseconds, bytes) ← decodeUInt 4 bytes
  let (orderId, bytes) ← decodeUInt 8 bytes
  let (orderBookId, bytes) ← decodeUInt 4 bytes
  let (side, bytes) ← Side.decode bytes
  pure ({ nanoseconds, orderId, orderBookId, side }, bytes)

@[simp] theorem encode_length (message : OrderDeleteMessage) : (encode message).length = 17 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Side.encode_length]

theorem encode_length_pos (message : OrderDeleteMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OrderDeleteMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [Side.decode_encode, some_bind]
  rfl

end OrderDeleteMessage

/-- Trade Message: 49 bytes -/
structure TradeMessage where
  nanoseconds : BitVec 32
  matchId : BitVec 96
  side : Side
  quantity : BitVec 64
  orderBookId : BitVec 32
  tradePrice : BitVec 32
  participantIdOwner : Alpha 7
  participantIdCounterparty : Alpha 7
  printable : Printable
  occurredAtCross : OccurredAtCross
  deriving DecidableEq, Repr

namespace TradeMessage

def encode (message : TradeMessage) : List UInt8 :=
  encodeUInt 4 message.nanoseconds
    ++ (encodeUInt 12 message.matchId
    ++ (Side.encode message.side
    ++ (encodeUInt 8 message.quantity
    ++ (encodeUInt 4 message.orderBookId
    ++ (encodeUInt 4 message.tradePrice
    ++ (Alpha.encode message.participantIdOwner
    ++ (Alpha.encode message.participantIdCounterparty
    ++ (Printable.encode message.printable
    ++ (OccurredAtCross.encode message.occurredAtCross)))))))))

def decode (bytes : List UInt8) : Option (TradeMessage × List UInt8) := do
  let (nanoseconds, bytes) ← decodeUInt 4 bytes
  let (matchId, bytes) ← decodeUInt 12 bytes
  let (side, bytes) ← Side.decode bytes
  let (quantity, bytes) ← decodeUInt 8 bytes
  let (orderBookId, bytes) ← decodeUInt 4 bytes
  let (tradePrice, bytes) ← decodeUInt 4 bytes
  let (participantIdOwner, bytes) ← Alpha.decode 7 bytes
  let (participantIdCounterparty, bytes) ← Alpha.decode 7 bytes
  let (printable, bytes) ← Printable.decode bytes
  let (occurredAtCross, bytes) ← OccurredAtCross.decode bytes
  pure ({ nanoseconds, matchId, side, quantity, orderBookId, tradePrice, participantIdOwner, participantIdCounterparty, printable, occurredAtCross }, bytes)

@[simp] theorem encode_length (message : TradeMessage) : (encode message).length = 49 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Side.encode_length, Alpha.encode_length, Printable.encode_length, OccurredAtCross.encode_length]

theorem encode_length_pos (message : TradeMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : TradeMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Side.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Printable.decode_encode, some_bind]
  dsimp only
  rw [OccurredAtCross.decode_encode, some_bind]
  rfl

end TradeMessage

/-- Equilibrium Price Update Message: 52 bytes -/
structure EquilibriumPriceUpdateMessage where
  nanoseconds : BitVec 32
  orderBookId : BitVec 32
  bidQuantity : BitVec 64
  askQuantity : BitVec 64
  equilibriumPrice : BitVec 32
  bestBidPrice : BitVec 32
  bestAskPrice : BitVec 32
  bestBidQuantity : BitVec 64
  bestAskQuantity : BitVec 64
  deriving DecidableEq, Repr

namespace EquilibriumPriceUpdateMessage

def encode (message : EquilibriumPriceUpdateMessage) : List UInt8 :=
  encodeUInt 4 message.nanoseconds
    ++ (encodeUInt 4 message.orderBookId
    ++ (encodeUInt 8 message.bidQuantity
    ++ (encodeUInt 8 message.askQuantity
    ++ (encodeUInt 4 message.equilibriumPrice
    ++ (encodeUInt 4 message.bestBidPrice
    ++ (encodeUInt 4 message.bestAskPrice
    ++ (encodeUInt 8 message.bestBidQuantity
    ++ (encodeUInt 8 message.bestAskQuantity))))))))

def decode (bytes : List UInt8) : Option (EquilibriumPriceUpdateMessage × List UInt8) := do
  let (nanoseconds, bytes) ← decodeUInt 4 bytes
  let (orderBookId, bytes) ← decodeUInt 4 bytes
  let (bidQuantity, bytes) ← decodeUInt 8 bytes
  let (askQuantity, bytes) ← decodeUInt 8 bytes
  let (equilibriumPrice, bytes) ← decodeUInt 4 bytes
  let (bestBidPrice, bytes) ← decodeUInt 4 bytes
  let (bestAskPrice, bytes) ← decodeUInt 4 bytes
  let (bestBidQuantity, bytes) ← decodeUInt 8 bytes
  let (bestAskQuantity, bytes) ← decodeUInt 8 bytes
  pure ({ nanoseconds, orderBookId, bidQuantity, askQuantity, equilibriumPrice, bestBidPrice, bestAskPrice, bestBidQuantity, bestAskQuantity }, bytes)

@[simp] theorem encode_length (message : EquilibriumPriceUpdateMessage) : (encode message).length = 52 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length]

theorem encode_length_pos (message : EquilibriumPriceUpdateMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : EquilibriumPriceUpdateMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end EquilibriumPriceUpdateMessage

/-- Any Payload, selected by Message Type -/
inductive Payload where
  | secondsMessage (message : SecondsMessage) -- "T" 0x54
  | orderBookDirectoryMessage (message : OrderBookDirectoryMessage) -- "R" 0x52
  | combinationOrderBookDirectoryMessage (message : CombinationOrderBookDirectoryMessage) -- "M" 0x4D
  | tickSizeMessage (message : TickSizeMessage) -- "L" 0x4C
  | systemEventMessage (message : SystemEventMessage) -- "S" 0x53
  | orderBookStateMessage (message : OrderBookStateMessage) -- "O" 0x4F
  | addOrderNoParticipantIdMessage (message : AddOrderNoParticipantIdMessage) -- "A" 0x41
  | addOrderParticipantIdMessage (message : AddOrderParticipantIdMessage) -- "F" 0x46
  | orderExecutedMessage (message : OrderExecutedMessage) -- "E" 0x45
  | orderExecutedWithPriceMessage (message : OrderExecutedWithPriceMessage) -- "C" 0x43
  | orderReplaceMessage (message : OrderReplaceMessage) -- "U" 0x55
  | orderDeleteMessage (message : OrderDeleteMessage) -- "D" 0x44
  | tradeMessage (message : TradeMessage) -- "P" 0x50
  | equilibriumPriceUpdateMessage (message : EquilibriumPriceUpdateMessage) -- "Z" 0x5A
  deriving DecidableEq, Repr

namespace Payload

/-- The Message Type each message is sent under -/
def tag : Payload → BitVec 8
  | .secondsMessage _ => 84
  | .orderBookDirectoryMessage _ => 82
  | .combinationOrderBookDirectoryMessage _ => 77
  | .tickSizeMessage _ => 76
  | .systemEventMessage _ => 83
  | .orderBookStateMessage _ => 79
  | .addOrderNoParticipantIdMessage _ => 65
  | .addOrderParticipantIdMessage _ => 70
  | .orderExecutedMessage _ => 69
  | .orderExecutedWithPriceMessage _ => 67
  | .orderReplaceMessage _ => 85
  | .orderDeleteMessage _ => 68
  | .tradeMessage _ => 80
  | .equilibriumPriceUpdateMessage _ => 90

def encode : Payload → List UInt8
  | .secondsMessage message => SecondsMessage.encode message
  | .orderBookDirectoryMessage message => OrderBookDirectoryMessage.encode message
  | .combinationOrderBookDirectoryMessage message => CombinationOrderBookDirectoryMessage.encode message
  | .tickSizeMessage message => TickSizeMessage.encode message
  | .systemEventMessage message => SystemEventMessage.encode message
  | .orderBookStateMessage message => OrderBookStateMessage.encode message
  | .addOrderNoParticipantIdMessage message => AddOrderNoParticipantIdMessage.encode message
  | .addOrderParticipantIdMessage message => AddOrderParticipantIdMessage.encode message
  | .orderExecutedMessage message => OrderExecutedMessage.encode message
  | .orderExecutedWithPriceMessage message => OrderExecutedWithPriceMessage.encode message
  | .orderReplaceMessage message => OrderReplaceMessage.encode message
  | .orderDeleteMessage message => OrderDeleteMessage.encode message
  | .tradeMessage message => TradeMessage.encode message
  | .equilibriumPriceUpdateMessage message => EquilibriumPriceUpdateMessage.encode message

/-- The most bytes any message's encoding can take -/
theorem encode_length_le (message : Payload) : (encode message).length ≤ 260 := by
  cases message with
  | secondsMessage inner =>
    simp only [encode, SecondsMessage.encode_length]
    omega
  | orderBookDirectoryMessage inner =>
    simp only [encode, OrderBookDirectoryMessage.encode_length]
    omega
  | combinationOrderBookDirectoryMessage inner =>
    simp only [encode, CombinationOrderBookDirectoryMessage.encode_length]
    omega
  | tickSizeMessage inner =>
    simp only [encode, TickSizeMessage.encode_length]
    omega
  | systemEventMessage inner =>
    simp only [encode, SystemEventMessage.encode_length]
    omega
  | orderBookStateMessage inner =>
    simp only [encode, OrderBookStateMessage.encode_length]
    omega
  | addOrderNoParticipantIdMessage inner =>
    simp only [encode, AddOrderNoParticipantIdMessage.encode_length]
    omega
  | addOrderParticipantIdMessage inner =>
    simp only [encode, AddOrderParticipantIdMessage.encode_length]
    omega
  | orderExecutedMessage inner =>
    simp only [encode, OrderExecutedMessage.encode_length]
    omega
  | orderExecutedWithPriceMessage inner =>
    simp only [encode, OrderExecutedWithPriceMessage.encode_length]
    omega
  | orderReplaceMessage inner =>
    simp only [encode, OrderReplaceMessage.encode_length]
    omega
  | orderDeleteMessage inner =>
    simp only [encode, OrderDeleteMessage.encode_length]
    omega
  | tradeMessage inner =>
    simp only [encode, TradeMessage.encode_length]
    omega
  | equilibriumPriceUpdateMessage inner =>
    simp only [encode, EquilibriumPriceUpdateMessage.encode_length]
    omega

def decode (tag : BitVec 8) (bytes : List UInt8) : Option (Payload × List UInt8) :=
  if tag = 84 then (SecondsMessage.decode bytes).map fun (message, rest) => (.secondsMessage message, rest)
  else if tag = 82 then (OrderBookDirectoryMessage.decode bytes).map fun (message, rest) => (.orderBookDirectoryMessage message, rest)
  else if tag = 77 then (CombinationOrderBookDirectoryMessage.decode bytes).map fun (message, rest) => (.combinationOrderBookDirectoryMessage message, rest)
  else if tag = 76 then (TickSizeMessage.decode bytes).map fun (message, rest) => (.tickSizeMessage message, rest)
  else if tag = 83 then (SystemEventMessage.decode bytes).map fun (message, rest) => (.systemEventMessage message, rest)
  else if tag = 79 then (OrderBookStateMessage.decode bytes).map fun (message, rest) => (.orderBookStateMessage message, rest)
  else if tag = 65 then (AddOrderNoParticipantIdMessage.decode bytes).map fun (message, rest) => (.addOrderNoParticipantIdMessage message, rest)
  else if tag = 70 then (AddOrderParticipantIdMessage.decode bytes).map fun (message, rest) => (.addOrderParticipantIdMessage message, rest)
  else if tag = 69 then (OrderExecutedMessage.decode bytes).map fun (message, rest) => (.orderExecutedMessage message, rest)
  else if tag = 67 then (OrderExecutedWithPriceMessage.decode bytes).map fun (message, rest) => (.orderExecutedWithPriceMessage message, rest)
  else if tag = 85 then (OrderReplaceMessage.decode bytes).map fun (message, rest) => (.orderReplaceMessage message, rest)
  else if tag = 68 then (OrderDeleteMessage.decode bytes).map fun (message, rest) => (.orderDeleteMessage message, rest)
  else if tag = 80 then (TradeMessage.decode bytes).map fun (message, rest) => (.tradeMessage message, rest)
  else if tag = 90 then (EquilibriumPriceUpdateMessage.decode bytes).map fun (message, rest) => (.equilibriumPriceUpdateMessage message, rest)
  else none

@[simp] theorem decode_encode (message : Payload) (rest : List UInt8) :
    decode (tag message) (encode message ++ rest) = some (message, rest) := by
  cases message <;> simp [decode, encode, tag]

end Payload

/-- Message -/
structure Message where
  payload : Payload
  deriving DecidableEq, Repr

namespace Message

def encodeBody (message : Message) : List UInt8 :=
  encodeUInt 1 (Payload.tag message.payload)
    ++ (Payload.encode message.payload)

def decodeBody (bytes : List UInt8) : Option (Message × List UInt8) := do
  let (messageType, bytes) ← decodeUInt 1 bytes
  let (payload, bytes) ← Payload.decode messageType bytes
  pure ({ payload }, bytes)

theorem decodeBody_encodeBody (message : Message) (rest : List UInt8) :
    decodeBody (encodeBody message ++ rest) = some (message, rest) := by
  unfold decodeBody encodeBody
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [Payload.decode_encode, some_bind]
  rfl

/-- Every body fits the length prefix -/
theorem encodeBody_length_lt (message : Message) : (encodeBody message).length + 0 < 256 ^ 2 := by
  unfold encodeBody
  cases message.payload with
  | secondsMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, SecondsMessage.encode_length]
    omega
  | orderBookDirectoryMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, OrderBookDirectoryMessage.encode_length]
    omega
  | combinationOrderBookDirectoryMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, CombinationOrderBookDirectoryMessage.encode_length]
    omega
  | tickSizeMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, TickSizeMessage.encode_length]
    omega
  | systemEventMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, SystemEventMessage.encode_length]
    omega
  | orderBookStateMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, OrderBookStateMessage.encode_length]
    omega
  | addOrderNoParticipantIdMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, AddOrderNoParticipantIdMessage.encode_length]
    omega
  | addOrderParticipantIdMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, AddOrderParticipantIdMessage.encode_length]
    omega
  | orderExecutedMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, OrderExecutedMessage.encode_length]
    omega
  | orderExecutedWithPriceMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, OrderExecutedWithPriceMessage.encode_length]
    omega
  | orderReplaceMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, OrderReplaceMessage.encode_length]
    omega
  | orderDeleteMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, OrderDeleteMessage.encode_length]
    omega
  | tradeMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, TradeMessage.encode_length]
    omega
  | equilibriumPriceUpdateMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, EquilibriumPriceUpdateMessage.encode_length]
    omega

/-- Size rule: Message Length counts the bytes after it, so it is written from the body and checked on decode -/
def encode : Message → List UInt8 :=
  encodeFramed 2 0 encodeBody

def decode : List UInt8 → Option (Message × List UInt8) :=
  decodeFramed 2 0 decodeBody

@[simp] theorem decode_encode (message : Message) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) :=
  decodeFramed_encodeFramed 2 0 encodeBody decodeBody message (decodeBody_encodeBody message) (encodeBody_length_lt message) rest

theorem encode_length_pos (message : Message) : (encode message).length > 0 := by
  unfold encode
  rw [encodeFramed_length]
  omega

end Message

/-- Packet -/
structure Packet where
  session : Alpha 10
  sequenceNumber : BitVec 64
  message : Bounded 2 Message
  deriving DecidableEq, Repr

namespace Packet

def encode (message : Packet) : List UInt8 :=
  Alpha.encode message.session
    ++ (encodeUInt 8 message.sequenceNumber
    ++ (encodeUInt 2 (BitVec.ofNat (8 * 2) message.message.val.length)
    ++ (encodeMany Message.encode message.message.val)))

def decode (bytes : List UInt8) : Option (Packet × List UInt8) := do
  let (session, bytes) ← Alpha.decode 10 bytes
  let (sequenceNumber, bytes) ← decodeUInt 8 bytes
  let (messageCount, bytes) ← decodeUInt 2 bytes
  let (message_, bytes) ← decodeMany Message.decode messageCount.toNat bytes
  if fits_message : message_.length < 256 ^ 2 then
    pure ({ session, sequenceNumber, message := ⟨message_, fits_message⟩ }, bytes)
  else none

theorem encode_length_pos (message : Packet) : (encode message).length > 0 := by
  unfold encode
  simp only [Alpha.encode_length, List.length_append, ← Nat.add_assoc]
  omega

@[simp] theorem decode_encode (message : Packet) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeMany_bounded 2 Message.encode Message.decode Message.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.message.length_lt]
  rfl

end Packet

end Omi.AsxAsxsecuritiesTradeItchV20
