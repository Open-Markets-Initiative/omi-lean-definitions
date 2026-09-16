import Omi.Wire

/-!
# Japan Exchange Group Genium Inet v5.0.6

Generated from the binary model, with the proofs the model's rules call for: every record
decodes back to what was encoded; a message dispatch selects the message its type names;
a count is written from the list it counts; a length prefix is written from the bytes it frames;
and a packet read to the end of its data decodes to the messages that were written.

Note: a Message Count of 0 marks Heartbeat and carries no messages; the decoder reads it as a count and the encoder never writes it.

Note: a Message Count of 65535 marks End Of Session and carries no messages; the decoder reads it as a count and the encoder never writes it.

Note: Order Attributes is a bit field set, proven as its 2 byte integer rather than bit by bit.

Text fields are kept byte for byte, padding included, so what is decoded encodes back unchanged.
Prices with implied decimals are proven as the integers on the wire.
-/

namespace Omi.JpxOsederivativesGeniuminetItchV506

/-- Leg Side: one byte code -/
def LegSide.codes : List UInt8 :=
  [0x42, 0x43]

inductive LegSide where
  | asDefined -- As Defined
  | opposite -- Opposite
  | unlisted (byte : { byte : UInt8 // byte ∉ LegSide.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace LegSide

def toByte : LegSide → UInt8
  | .asDefined => 0x42
  | .opposite => 0x43
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : LegSide :=
  if byte = 0x42 then .asDefined
  else .opposite

def ofByte (byte : UInt8) : LegSide :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : LegSide) : ofByte value.toByte = value := by
  cases value with
  | asDefined => decide
  | opposite => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : LegSide) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (LegSide × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : LegSide) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : LegSide) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end LegSide

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
  [0x42, 0x53]

inductive Side where
  | buyOrder -- Buy Order
  | sellOrder -- Sell Order
  | unlisted (byte : { byte : UInt8 // byte ∉ Side.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace Side

def toByte : Side → UInt8
  | .buyOrder => 0x42
  | .sellOrder => 0x53
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : Side :=
  if byte = 0x42 then .buyOrder
  else .sellOrder

def ofByte (byte : UInt8) : Side :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : Side) : ofByte value.toByte = value := by
  cases value with
  | buyOrder => decide
  | sellOrder => decide
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
  [0x4E, 0x59]

inductive OccurredAtCross where
  | no -- No
  | yes -- Yes
  | unlisted (byte : { byte : UInt8 // byte ∉ OccurredAtCross.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace OccurredAtCross

def toByte : OccurredAtCross → UInt8
  | .no => 0x4E
  | .yes => 0x59
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : OccurredAtCross :=
  if byte = 0x4E then .no
  else .yes

def ofByte (byte : UInt8) : OccurredAtCross :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : OccurredAtCross) : ofByte value.toByte = value := by
  cases value with
  | no => decide
  | yes => decide
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
  [0x4E, 0x59]

inductive Printable where
  | nonPrintable -- Non Printable
  | printable -- Printable
  | unlisted (byte : { byte : UInt8 // byte ∉ Printable.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace Printable

def toByte : Printable → UInt8
  | .nonPrintable => 0x4E
  | .printable => 0x59
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : Printable :=
  if byte = 0x4E then .nonPrintable
  else .printable

def ofByte (byte : UInt8) : Printable :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : Printable) : ofByte value.toByte = value := by
  cases value with
  | nonPrintable => decide
  | printable => decide
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
  seconds : BitVec 32
  deriving DecidableEq, Repr

namespace SecondsMessage

def encode (message : SecondsMessage) : List UInt8 :=
  encodeUInt 4 message.seconds

def decode (bytes : List UInt8) : Option (SecondsMessage × List UInt8) := do
  let (seconds, bytes) ← decodeUInt 4 bytes
  pure ({ seconds }, bytes)

@[simp] theorem encode_length (message : SecondsMessage) : (encode message).length = 4 := by
  unfold encode
  simp only [encodeUInt_length]

theorem encode_length_pos (message : SecondsMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SecondsMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [Option.bind_eq_bind]
  rw [decodeUInt_encodeUInt, Option.bind_some]
  rfl

end SecondsMessage

/-- Order Book Directory: 128 bytes -/
structure OrderBookDirectory where
  nanoseconds : BitVec 32
  orderBookId : BitVec 32
  symbol : Alpha 32
  longName : Alpha 32
  isin : Alpha 12
  financialProduct : BitVec 8
  tradingCurrency : Alpha 3
  decimalsInPrice : BitVec 16
  decimalsInNominalValue : BitVec 16
  oddLotSize : BitVec 32
  roundLotSize : BitVec 32
  blockLotSize : BitVec 32
  nominalValue : BitVec 64
  numberOfLegs : BitVec 8
  underlyingOrderbookId : BitVec 32
  strikePrice : BitVec 32
  expirationDate : BitVec 32
  decimalsInStrikePrice : BitVec 16
  putOrCall : BitVec 8
  deriving DecidableEq, Repr

namespace OrderBookDirectory

def encode (message : OrderBookDirectory) : List UInt8 :=
  encodeUInt 4 message.nanoseconds
    ++ encodeUInt 4 message.orderBookId
    ++ Alpha.encode message.symbol
    ++ Alpha.encode message.longName
    ++ Alpha.encode message.isin
    ++ encodeUInt 1 message.financialProduct
    ++ Alpha.encode message.tradingCurrency
    ++ encodeUInt 2 message.decimalsInPrice
    ++ encodeUInt 2 message.decimalsInNominalValue
    ++ encodeUInt 4 message.oddLotSize
    ++ encodeUInt 4 message.roundLotSize
    ++ encodeUInt 4 message.blockLotSize
    ++ encodeUInt 8 message.nominalValue
    ++ encodeUInt 1 message.numberOfLegs
    ++ encodeUInt 4 message.underlyingOrderbookId
    ++ encodeUInt 4 message.strikePrice
    ++ encodeUInt 4 message.expirationDate
    ++ encodeUInt 2 message.decimalsInStrikePrice
    ++ encodeUInt 1 message.putOrCall

def decode (bytes : List UInt8) : Option (OrderBookDirectory × List UInt8) := do
  let (nanoseconds, bytes) ← decodeUInt 4 bytes
  let (orderBookId, bytes) ← decodeUInt 4 bytes
  let (symbol, bytes) ← Alpha.decode 32 bytes
  let (longName, bytes) ← Alpha.decode 32 bytes
  let (isin, bytes) ← Alpha.decode 12 bytes
  let (financialProduct, bytes) ← decodeUInt 1 bytes
  let (tradingCurrency, bytes) ← Alpha.decode 3 bytes
  let (decimalsInPrice, bytes) ← decodeUInt 2 bytes
  let (decimalsInNominalValue, bytes) ← decodeUInt 2 bytes
  let (oddLotSize, bytes) ← decodeUInt 4 bytes
  let (roundLotSize, bytes) ← decodeUInt 4 bytes
  let (blockLotSize, bytes) ← decodeUInt 4 bytes
  let (nominalValue, bytes) ← decodeUInt 8 bytes
  let (numberOfLegs, bytes) ← decodeUInt 1 bytes
  let (underlyingOrderbookId, bytes) ← decodeUInt 4 bytes
  let (strikePrice, bytes) ← decodeUInt 4 bytes
  let (expirationDate, bytes) ← decodeUInt 4 bytes
  let (decimalsInStrikePrice, bytes) ← decodeUInt 2 bytes
  let (putOrCall, bytes) ← decodeUInt 1 bytes
  pure ({ nanoseconds, orderBookId, symbol, longName, isin, financialProduct, tradingCurrency, decimalsInPrice, decimalsInNominalValue, oddLotSize, roundLotSize, blockLotSize, nominalValue, numberOfLegs, underlyingOrderbookId, strikePrice, expirationDate, decimalsInStrikePrice, putOrCall }, bytes)

@[simp] theorem encode_length (message : OrderBookDirectory) : (encode message).length = 128 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Alpha.encode_length]

theorem encode_length_pos (message : OrderBookDirectory) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OrderBookDirectory) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt, Option.bind_some]
  rfl

end OrderBookDirectory

/-- Combination Orderbook Leg: 17 bytes -/
structure CombinationOrderbookLeg where
  nanoseconds : BitVec 32
  combinationOrderbookId : BitVec 32
  legOrderbookId : BitVec 32
  legSide : LegSide
  legRatio : BitVec 32
  deriving DecidableEq, Repr

namespace CombinationOrderbookLeg

def encode (message : CombinationOrderbookLeg) : List UInt8 :=
  encodeUInt 4 message.nanoseconds
    ++ encodeUInt 4 message.combinationOrderbookId
    ++ encodeUInt 4 message.legOrderbookId
    ++ LegSide.encode message.legSide
    ++ encodeUInt 4 message.legRatio

def decode (bytes : List UInt8) : Option (CombinationOrderbookLeg × List UInt8) := do
  let (nanoseconds, bytes) ← decodeUInt 4 bytes
  let (combinationOrderbookId, bytes) ← decodeUInt 4 bytes
  let (legOrderbookId, bytes) ← decodeUInt 4 bytes
  let (legSide, bytes) ← LegSide.decode bytes
  let (legRatio, bytes) ← decodeUInt 4 bytes
  pure ({ nanoseconds, combinationOrderbookId, legOrderbookId, legSide, legRatio }, bytes)

@[simp] theorem encode_length (message : CombinationOrderbookLeg) : (encode message).length = 17 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, LegSide.encode_length]

theorem encode_length_pos (message : CombinationOrderbookLeg) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : CombinationOrderbookLeg) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [LegSide.decode_encode]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt, Option.bind_some]
  rfl

end CombinationOrderbookLeg

/-- Tick Size Table Entry: 24 bytes -/
structure TickSizeTableEntry where
  nanoseconds : BitVec 32
  orderBookId : BitVec 32
  tickSize : BitVec 64
  priceFrom : BitVec 32
  priceTo : BitVec 32
  deriving DecidableEq, Repr

namespace TickSizeTableEntry

def encode (message : TickSizeTableEntry) : List UInt8 :=
  encodeUInt 4 message.nanoseconds
    ++ encodeUInt 4 message.orderBookId
    ++ encodeUInt 8 message.tickSize
    ++ encodeUInt 4 message.priceFrom
    ++ encodeUInt 4 message.priceTo

def decode (bytes : List UInt8) : Option (TickSizeTableEntry × List UInt8) := do
  let (nanoseconds, bytes) ← decodeUInt 4 bytes
  let (orderBookId, bytes) ← decodeUInt 4 bytes
  let (tickSize, bytes) ← decodeUInt 8 bytes
  let (priceFrom, bytes) ← decodeUInt 4 bytes
  let (priceTo, bytes) ← decodeUInt 4 bytes
  pure ({ nanoseconds, orderBookId, tickSize, priceFrom, priceTo }, bytes)

@[simp] theorem encode_length (message : TickSizeTableEntry) : (encode message).length = 24 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length]

theorem encode_length_pos (message : TickSizeTableEntry) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : TickSizeTableEntry) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt, Option.bind_some]
  rfl

end TickSizeTableEntry

/-- System Event Message: 5 bytes -/
structure SystemEventMessage where
  nanoseconds : BitVec 32
  eventCode : EventCode
  deriving DecidableEq, Repr

namespace SystemEventMessage

def encode (message : SystemEventMessage) : List UInt8 :=
  encodeUInt 4 message.nanoseconds
    ++ EventCode.encode message.eventCode

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
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [EventCode.decode_encode, Option.bind_some]
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
    ++ encodeUInt 4 message.orderBookId
    ++ Alpha.encode message.stateName

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
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode, Option.bind_some]
  rfl

end OrderBookStateMessage

/-- Add Order No Mpid: 36 bytes -/
structure AddOrderNoMpid where
  nanoseconds : BitVec 32
  orderId : BitVec 64
  orderBookId : BitVec 32
  side : Side
  orderBookPosition : BitVec 32
  quantity : BitVec 64
  price : BitVec 32
  orderAttributes : BitVec 16
  lotType : BitVec 8
  deriving DecidableEq, Repr

namespace AddOrderNoMpid

def encode (message : AddOrderNoMpid) : List UInt8 :=
  encodeUInt 4 message.nanoseconds
    ++ encodeUInt 8 message.orderId
    ++ encodeUInt 4 message.orderBookId
    ++ Side.encode message.side
    ++ encodeUInt 4 message.orderBookPosition
    ++ encodeUInt 8 message.quantity
    ++ encodeUInt 4 message.price
    ++ encodeUIntLE 2 message.orderAttributes
    ++ encodeUInt 1 message.lotType

def decode (bytes : List UInt8) : Option (AddOrderNoMpid × List UInt8) := do
  let (nanoseconds, bytes) ← decodeUInt 4 bytes
  let (orderId, bytes) ← decodeUInt 8 bytes
  let (orderBookId, bytes) ← decodeUInt 4 bytes
  let (side, bytes) ← Side.decode bytes
  let (orderBookPosition, bytes) ← decodeUInt 4 bytes
  let (quantity, bytes) ← decodeUInt 8 bytes
  let (price, bytes) ← decodeUInt 4 bytes
  let (orderAttributes, bytes) ← decodeUIntLE 2 bytes
  let (lotType, bytes) ← decodeUInt 1 bytes
  pure ({ nanoseconds, orderId, orderBookId, side, orderBookPosition, quantity, price, orderAttributes, lotType }, bytes)

@[simp] theorem encode_length (message : AddOrderNoMpid) : (encode message).length = 36 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Side.encode_length, encodeUIntLE_length]

theorem encode_length_pos (message : AddOrderNoMpid) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : AddOrderNoMpid) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [Side.decode_encode]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt, Option.bind_some]
  rfl

end AddOrderNoMpid

/-- Add Order With Mpid: 43 bytes -/
structure AddOrderWithMpid where
  nanoseconds : BitVec 32
  orderId : BitVec 64
  orderBookId : BitVec 32
  side : Side
  orderBookPosition : BitVec 32
  quantity : BitVec 64
  price : BitVec 32
  orderAttributes : BitVec 16
  lotType : BitVec 8
  participantId : Alpha 7
  deriving DecidableEq, Repr

namespace AddOrderWithMpid

def encode (message : AddOrderWithMpid) : List UInt8 :=
  encodeUInt 4 message.nanoseconds
    ++ encodeUInt 8 message.orderId
    ++ encodeUInt 4 message.orderBookId
    ++ Side.encode message.side
    ++ encodeUInt 4 message.orderBookPosition
    ++ encodeUInt 8 message.quantity
    ++ encodeUInt 4 message.price
    ++ encodeUIntLE 2 message.orderAttributes
    ++ encodeUInt 1 message.lotType
    ++ Alpha.encode message.participantId

def decode (bytes : List UInt8) : Option (AddOrderWithMpid × List UInt8) := do
  let (nanoseconds, bytes) ← decodeUInt 4 bytes
  let (orderId, bytes) ← decodeUInt 8 bytes
  let (orderBookId, bytes) ← decodeUInt 4 bytes
  let (side, bytes) ← Side.decode bytes
  let (orderBookPosition, bytes) ← decodeUInt 4 bytes
  let (quantity, bytes) ← decodeUInt 8 bytes
  let (price, bytes) ← decodeUInt 4 bytes
  let (orderAttributes, bytes) ← decodeUIntLE 2 bytes
  let (lotType, bytes) ← decodeUInt 1 bytes
  let (participantId, bytes) ← Alpha.decode 7 bytes
  pure ({ nanoseconds, orderId, orderBookId, side, orderBookPosition, quantity, price, orderAttributes, lotType, participantId }, bytes)

@[simp] theorem encode_length (message : AddOrderWithMpid) : (encode message).length = 43 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Side.encode_length, encodeUIntLE_length, Alpha.encode_length]

theorem encode_length_pos (message : AddOrderWithMpid) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : AddOrderWithMpid) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [Side.decode_encode]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode, Option.bind_some]
  rfl

end AddOrderWithMpid

/-- Order Executed Message: 51 bytes -/
structure OrderExecutedMessage where
  nanoseconds : BitVec 32
  orderId : BitVec 64
  orderBookId : BitVec 32
  side : Side
  executedQuantity : BitVec 64
  matchId : BitVec 64
  comboGroupId : BitVec 32
  participantIdOwner : Alpha 7
  participantIdCounterparty : Alpha 7
  deriving DecidableEq, Repr

namespace OrderExecutedMessage

def encode (message : OrderExecutedMessage) : List UInt8 :=
  encodeUInt 4 message.nanoseconds
    ++ encodeUInt 8 message.orderId
    ++ encodeUInt 4 message.orderBookId
    ++ Side.encode message.side
    ++ encodeUInt 8 message.executedQuantity
    ++ encodeUInt 8 message.matchId
    ++ encodeUInt 4 message.comboGroupId
    ++ Alpha.encode message.participantIdOwner
    ++ Alpha.encode message.participantIdCounterparty

def decode (bytes : List UInt8) : Option (OrderExecutedMessage × List UInt8) := do
  let (nanoseconds, bytes) ← decodeUInt 4 bytes
  let (orderId, bytes) ← decodeUInt 8 bytes
  let (orderBookId, bytes) ← decodeUInt 4 bytes
  let (side, bytes) ← Side.decode bytes
  let (executedQuantity, bytes) ← decodeUInt 8 bytes
  let (matchId, bytes) ← decodeUInt 8 bytes
  let (comboGroupId, bytes) ← decodeUInt 4 bytes
  let (participantIdOwner, bytes) ← Alpha.decode 7 bytes
  let (participantIdCounterparty, bytes) ← Alpha.decode 7 bytes
  pure ({ nanoseconds, orderId, orderBookId, side, executedQuantity, matchId, comboGroupId, participantIdOwner, participantIdCounterparty }, bytes)

@[simp] theorem encode_length (message : OrderExecutedMessage) : (encode message).length = 51 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Side.encode_length, Alpha.encode_length]

theorem encode_length_pos (message : OrderExecutedMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OrderExecutedMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [Side.decode_encode]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode, Option.bind_some]
  rfl

end OrderExecutedMessage

/-- Order Executed With Price Message: 57 bytes -/
structure OrderExecutedWithPriceMessage where
  nanoseconds : BitVec 32
  orderId : BitVec 64
  orderBookId : BitVec 32
  side : Side
  executedQuantity : BitVec 64
  matchId : BitVec 64
  comboGroupId : BitVec 32
  ownerParticipantId : Alpha 7
  counterpartyParticipantId : Alpha 7
  tradePrice : BitVec 32
  occurredAtCross : OccurredAtCross
  printable : Printable
  deriving DecidableEq, Repr

namespace OrderExecutedWithPriceMessage

def encode (message : OrderExecutedWithPriceMessage) : List UInt8 :=
  encodeUInt 4 message.nanoseconds
    ++ encodeUInt 8 message.orderId
    ++ encodeUInt 4 message.orderBookId
    ++ Side.encode message.side
    ++ encodeUInt 8 message.executedQuantity
    ++ encodeUInt 8 message.matchId
    ++ encodeUInt 4 message.comboGroupId
    ++ Alpha.encode message.ownerParticipantId
    ++ Alpha.encode message.counterpartyParticipantId
    ++ encodeUInt 4 message.tradePrice
    ++ OccurredAtCross.encode message.occurredAtCross
    ++ Printable.encode message.printable

def decode (bytes : List UInt8) : Option (OrderExecutedWithPriceMessage × List UInt8) := do
  let (nanoseconds, bytes) ← decodeUInt 4 bytes
  let (orderId, bytes) ← decodeUInt 8 bytes
  let (orderBookId, bytes) ← decodeUInt 4 bytes
  let (side, bytes) ← Side.decode bytes
  let (executedQuantity, bytes) ← decodeUInt 8 bytes
  let (matchId, bytes) ← decodeUInt 8 bytes
  let (comboGroupId, bytes) ← decodeUInt 4 bytes
  let (ownerParticipantId, bytes) ← Alpha.decode 7 bytes
  let (counterpartyParticipantId, bytes) ← Alpha.decode 7 bytes
  let (tradePrice, bytes) ← decodeUInt 4 bytes
  let (occurredAtCross, bytes) ← OccurredAtCross.decode bytes
  let (printable_, bytes) ← Printable.decode bytes
  pure ({ nanoseconds, orderId, orderBookId, side, executedQuantity, matchId, comboGroupId, ownerParticipantId, counterpartyParticipantId, tradePrice, occurredAtCross, printable := printable_ }, bytes)

@[simp] theorem encode_length (message : OrderExecutedWithPriceMessage) : (encode message).length = 57 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Side.encode_length, Alpha.encode_length, OccurredAtCross.encode_length, Printable.encode_length]

theorem encode_length_pos (message : OrderExecutedWithPriceMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OrderExecutedWithPriceMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [Side.decode_encode]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [OccurredAtCross.decode_encode]
  simp only [Option.bind_some]
  rw [Printable.decode_encode, Option.bind_some]
  rfl

end OrderExecutedWithPriceMessage

/-- Order Replace Message: 35 bytes -/
structure OrderReplaceMessage where
  nanoseconds : BitVec 32
  orderId : BitVec 64
  orderBookId : BitVec 32
  side : Side
  newOrderbookPosition : BitVec 32
  quantity : BitVec 64
  price : BitVec 32
  orderAttributes : BitVec 16
  deriving DecidableEq, Repr

namespace OrderReplaceMessage

def encode (message : OrderReplaceMessage) : List UInt8 :=
  encodeUInt 4 message.nanoseconds
    ++ encodeUInt 8 message.orderId
    ++ encodeUInt 4 message.orderBookId
    ++ Side.encode message.side
    ++ encodeUInt 4 message.newOrderbookPosition
    ++ encodeUInt 8 message.quantity
    ++ encodeUInt 4 message.price
    ++ encodeUIntLE 2 message.orderAttributes

def decode (bytes : List UInt8) : Option (OrderReplaceMessage × List UInt8) := do
  let (nanoseconds, bytes) ← decodeUInt 4 bytes
  let (orderId, bytes) ← decodeUInt 8 bytes
  let (orderBookId, bytes) ← decodeUInt 4 bytes
  let (side, bytes) ← Side.decode bytes
  let (newOrderbookPosition, bytes) ← decodeUInt 4 bytes
  let (quantity, bytes) ← decodeUInt 8 bytes
  let (price, bytes) ← decodeUInt 4 bytes
  let (orderAttributes, bytes) ← decodeUIntLE 2 bytes
  pure ({ nanoseconds, orderId, orderBookId, side, newOrderbookPosition, quantity, price, orderAttributes }, bytes)

@[simp] theorem encode_length (message : OrderReplaceMessage) : (encode message).length = 35 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Side.encode_length, encodeUIntLE_length]

theorem encode_length_pos (message : OrderReplaceMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OrderReplaceMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [Side.decode_encode]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE, Option.bind_some]
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
    ++ encodeUInt 8 message.orderId
    ++ encodeUInt 4 message.orderBookId
    ++ Side.encode message.side

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
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [Side.decode_encode, Option.bind_some]
  rfl

end OrderDeleteMessage

/-- Trade Message: 49 bytes -/
structure TradeMessage where
  nanoseconds : BitVec 32
  matchId : BitVec 64
  comboGroupId : BitVec 32
  side : Side
  quantity : BitVec 64
  orderBookId : BitVec 32
  tradePrice : BitVec 32
  ownerParticipantId : Alpha 7
  counterpartyParticipantId : Alpha 7
  printable : Printable
  occurredAtCross : OccurredAtCross
  deriving DecidableEq, Repr

namespace TradeMessage

def encode (message : TradeMessage) : List UInt8 :=
  encodeUInt 4 message.nanoseconds
    ++ encodeUInt 8 message.matchId
    ++ encodeUInt 4 message.comboGroupId
    ++ Side.encode message.side
    ++ encodeUInt 8 message.quantity
    ++ encodeUInt 4 message.orderBookId
    ++ encodeUInt 4 message.tradePrice
    ++ Alpha.encode message.ownerParticipantId
    ++ Alpha.encode message.counterpartyParticipantId
    ++ Printable.encode message.printable
    ++ OccurredAtCross.encode message.occurredAtCross

def decode (bytes : List UInt8) : Option (TradeMessage × List UInt8) := do
  let (nanoseconds, bytes) ← decodeUInt 4 bytes
  let (matchId, bytes) ← decodeUInt 8 bytes
  let (comboGroupId, bytes) ← decodeUInt 4 bytes
  let (side, bytes) ← Side.decode bytes
  let (quantity, bytes) ← decodeUInt 8 bytes
  let (orderBookId, bytes) ← decodeUInt 4 bytes
  let (tradePrice, bytes) ← decodeUInt 4 bytes
  let (ownerParticipantId, bytes) ← Alpha.decode 7 bytes
  let (counterpartyParticipantId, bytes) ← Alpha.decode 7 bytes
  let (printable_, bytes) ← Printable.decode bytes
  let (occurredAtCross, bytes) ← OccurredAtCross.decode bytes
  pure ({ nanoseconds, matchId, comboGroupId, side, quantity, orderBookId, tradePrice, ownerParticipantId, counterpartyParticipantId, printable := printable_, occurredAtCross }, bytes)

@[simp] theorem encode_length (message : TradeMessage) : (encode message).length = 49 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Side.encode_length, Alpha.encode_length, Printable.encode_length, OccurredAtCross.encode_length]

theorem encode_length_pos (message : TradeMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : TradeMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [Side.decode_encode]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [Printable.decode_encode]
  simp only [Option.bind_some]
  rw [OccurredAtCross.decode_encode, Option.bind_some]
  rfl

end TradeMessage

/-- Equilibrium Price Update: 52 bytes -/
structure EquilibriumPriceUpdate where
  nanoseconds : BitVec 32
  orderBookId : BitVec 32
  availableBidQuantityAtEquilibriumPrice : BitVec 64
  availableAskQuantityAtEquilibriumPrice : BitVec 64
  equilibriumPrice : BitVec 32
  reserved24 : Alpha 24
  deriving DecidableEq, Repr

namespace EquilibriumPriceUpdate

def encode (message : EquilibriumPriceUpdate) : List UInt8 :=
  encodeUInt 4 message.nanoseconds
    ++ encodeUInt 4 message.orderBookId
    ++ encodeUInt 8 message.availableBidQuantityAtEquilibriumPrice
    ++ encodeUInt 8 message.availableAskQuantityAtEquilibriumPrice
    ++ encodeUInt 4 message.equilibriumPrice
    ++ Alpha.encode message.reserved24

def decode (bytes : List UInt8) : Option (EquilibriumPriceUpdate × List UInt8) := do
  let (nanoseconds, bytes) ← decodeUInt 4 bytes
  let (orderBookId, bytes) ← decodeUInt 4 bytes
  let (availableBidQuantityAtEquilibriumPrice, bytes) ← decodeUInt 8 bytes
  let (availableAskQuantityAtEquilibriumPrice, bytes) ← decodeUInt 8 bytes
  let (equilibriumPrice, bytes) ← decodeUInt 4 bytes
  let (reserved24, bytes) ← Alpha.decode 24 bytes
  pure ({ nanoseconds, orderBookId, availableBidQuantityAtEquilibriumPrice, availableAskQuantityAtEquilibriumPrice, equilibriumPrice, reserved24 }, bytes)

@[simp] theorem encode_length (message : EquilibriumPriceUpdate) : (encode message).length = 52 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Alpha.encode_length]

theorem encode_length_pos (message : EquilibriumPriceUpdate) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : EquilibriumPriceUpdate) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode, Option.bind_some]
  rfl

end EquilibriumPriceUpdate

/-- Any Payload, selected by Message Type -/
inductive Payload where
  | secondsMessage (message : SecondsMessage) -- 'T' 0x54
  | orderBookDirectory (message : OrderBookDirectory) -- 'R' 0x52
  | combinationOrderbookLeg (message : CombinationOrderbookLeg) -- 'M' 0x4D
  | tickSizeTableEntry (message : TickSizeTableEntry) -- 'L' 0x4C
  | systemEventMessage (message : SystemEventMessage) -- 'S' 0x53
  | orderBookStateMessage (message : OrderBookStateMessage) -- 'O' 0x4F
  | addOrderNoMpid (message : AddOrderNoMpid) -- 'A' 0x41
  | addOrderWithMpid (message : AddOrderWithMpid) -- 'F' 0x46
  | orderExecutedMessage (message : OrderExecutedMessage) -- 'E' 0x45
  | orderExecutedWithPriceMessage (message : OrderExecutedWithPriceMessage) -- 'C' 0x43
  | orderReplaceMessage (message : OrderReplaceMessage) -- 'U' 0x55
  | orderDeleteMessage (message : OrderDeleteMessage) -- 'D' 0x44
  | tradeMessage (message : TradeMessage) -- 'P' 0x50
  | equilibriumPriceUpdate (message : EquilibriumPriceUpdate) -- 'Z' 0x5A
  deriving DecidableEq, Repr

namespace Payload

/-- The Message Type each message is sent under -/
def tag : Payload → BitVec 8
  | .secondsMessage _ => 84
  | .orderBookDirectory _ => 82
  | .combinationOrderbookLeg _ => 77
  | .tickSizeTableEntry _ => 76
  | .systemEventMessage _ => 83
  | .orderBookStateMessage _ => 79
  | .addOrderNoMpid _ => 65
  | .addOrderWithMpid _ => 70
  | .orderExecutedMessage _ => 69
  | .orderExecutedWithPriceMessage _ => 67
  | .orderReplaceMessage _ => 85
  | .orderDeleteMessage _ => 68
  | .tradeMessage _ => 80
  | .equilibriumPriceUpdate _ => 90

def encode : Payload → List UInt8
  | .secondsMessage message => SecondsMessage.encode message
  | .orderBookDirectory message => OrderBookDirectory.encode message
  | .combinationOrderbookLeg message => CombinationOrderbookLeg.encode message
  | .tickSizeTableEntry message => TickSizeTableEntry.encode message
  | .systemEventMessage message => SystemEventMessage.encode message
  | .orderBookStateMessage message => OrderBookStateMessage.encode message
  | .addOrderNoMpid message => AddOrderNoMpid.encode message
  | .addOrderWithMpid message => AddOrderWithMpid.encode message
  | .orderExecutedMessage message => OrderExecutedMessage.encode message
  | .orderExecutedWithPriceMessage message => OrderExecutedWithPriceMessage.encode message
  | .orderReplaceMessage message => OrderReplaceMessage.encode message
  | .orderDeleteMessage message => OrderDeleteMessage.encode message
  | .tradeMessage message => TradeMessage.encode message
  | .equilibriumPriceUpdate message => EquilibriumPriceUpdate.encode message

def decode (tag : BitVec 8) (bytes : List UInt8) : Option (Payload × List UInt8) :=
  if tag = 84 then (SecondsMessage.decode bytes).map fun (message, rest) => (.secondsMessage message, rest)
  else if tag = 82 then (OrderBookDirectory.decode bytes).map fun (message, rest) => (.orderBookDirectory message, rest)
  else if tag = 77 then (CombinationOrderbookLeg.decode bytes).map fun (message, rest) => (.combinationOrderbookLeg message, rest)
  else if tag = 76 then (TickSizeTableEntry.decode bytes).map fun (message, rest) => (.tickSizeTableEntry message, rest)
  else if tag = 83 then (SystemEventMessage.decode bytes).map fun (message, rest) => (.systemEventMessage message, rest)
  else if tag = 79 then (OrderBookStateMessage.decode bytes).map fun (message, rest) => (.orderBookStateMessage message, rest)
  else if tag = 65 then (AddOrderNoMpid.decode bytes).map fun (message, rest) => (.addOrderNoMpid message, rest)
  else if tag = 70 then (AddOrderWithMpid.decode bytes).map fun (message, rest) => (.addOrderWithMpid message, rest)
  else if tag = 69 then (OrderExecutedMessage.decode bytes).map fun (message, rest) => (.orderExecutedMessage message, rest)
  else if tag = 67 then (OrderExecutedWithPriceMessage.decode bytes).map fun (message, rest) => (.orderExecutedWithPriceMessage message, rest)
  else if tag = 85 then (OrderReplaceMessage.decode bytes).map fun (message, rest) => (.orderReplaceMessage message, rest)
  else if tag = 68 then (OrderDeleteMessage.decode bytes).map fun (message, rest) => (.orderDeleteMessage message, rest)
  else if tag = 80 then (TradeMessage.decode bytes).map fun (message, rest) => (.tradeMessage message, rest)
  else if tag = 90 then (EquilibriumPriceUpdate.decode bytes).map fun (message, rest) => (.equilibriumPriceUpdate message, rest)
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
    ++ Payload.encode message.payload

def decodeBody (bytes : List UInt8) : Option (Message × List UInt8) := do
  let (messageType, bytes) ← decodeUInt 1 bytes
  let (payload, bytes) ← Payload.decode messageType bytes
  pure ({ payload }, bytes)

theorem decodeBody_encodeBody (message : Message) (rest : List UInt8) :
    decodeBody (encodeBody message ++ rest) = some (message, rest) := by
  unfold decodeBody encodeBody
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [Payload.decode_encode, Option.bind_some]
  rfl

/-- Every body fits the length prefix -/
theorem encodeBody_length_lt (message : Message) : (encodeBody message).length + 0 < 256 ^ 2 := by
  unfold encodeBody
  cases message.payload with
  | secondsMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, SecondsMessage.encode_length]
    omega
  | orderBookDirectory inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, OrderBookDirectory.encode_length]
    omega
  | combinationOrderbookLeg inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, CombinationOrderbookLeg.encode_length]
    omega
  | tickSizeTableEntry inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, TickSizeTableEntry.encode_length]
    omega
  | systemEventMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, SystemEventMessage.encode_length]
    omega
  | orderBookStateMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, OrderBookStateMessage.encode_length]
    omega
  | addOrderNoMpid inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, AddOrderNoMpid.encode_length]
    omega
  | addOrderWithMpid inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, AddOrderWithMpid.encode_length]
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
  | equilibriumPriceUpdate inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, EquilibriumPriceUpdate.encode_length]
    omega

/-- Size rule: Message Length counts the bytes after it, so it is written from the body and checked on decode -/
def encode : Message → List UInt8 :=
  encodeFramed 2 0 encodeBody

def decode : List UInt8 → Option (Message × List UInt8) :=
  decodeFramed 2 0 decodeBody

@[simp] theorem decode_encode (message : Message) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) :=
  decodeFramed_encodeFramed 2 0 encodeBody decodeBody decodeBody_encodeBody encodeBody_length_lt message rest

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
    ++ encodeUInt 8 message.sequenceNumber
    ++ encodeUInt 2 (BitVec.ofNat (8 * 2) message.message.val.length)
    ++ encodeMany Message.encode message.message.val

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
  simp only [Alpha.encode_length, List.length_append]
  omega

@[simp] theorem decode_encode (message : Packet) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeMany_bounded 2 Message.encode Message.decode Message.decode_encode]
  simp only [Option.bind_some]
  simp only [message.message.length_lt, ↓reduceDIte]
  rfl

end Packet

end Omi.JpxOsederivativesGeniuminetItchV506
