import Omi.Wire

/-!
# National Association of Securities Dealers Automated Quotations (Nasdaq) Nordic Equity TotalView v3.00.1

Generated from the binary model, with the proofs the model's rules call for: every record
decodes back to what was encoded; a message dispatch selects the message its type names;
a count is written from the list it counts; a length prefix is written from the bytes it frames;
and a packet read to the end of its data decodes to the messages that were written.

Note: Note Codes Bit Field 1 is a bit field set, proven as its 1 byte integer rather than bit by bit.

Note: Note Codes Bit Field 2 is a bit field set, proven as its 1 byte integer rather than bit by bit.

Note: Note Codes Bit Field 3 is a bit field set, proven as its 1 byte integer rather than bit by bit.

Note: Note Codes Bit Field 4 is a bit field set, proven as its 1 byte integer rather than bit by bit.

Note: Note Codes Bit Field 5 is a bit field set, proven as its 1 byte integer rather than bit by bit.

Note: Note Codes Bit Field 6 is a bit field set, proven as its 1 byte integer rather than bit by bit.

Note: Note Codes Bit Field 7 is a bit field set, proven as its 1 byte integer rather than bit by bit.

Note: Note Codes Bit Field 8 is a bit field set, proven as its 1 byte integer rather than bit by bit.

Note: Sequenced Data Packet is not framed: its length Packet Length is not an integer it reads.

Text fields are kept byte for byte, padding included, so what is decoded encodes back unchanged.
Prices with implied decimals are proven as the integers on the wire.
-/

namespace Omi.NasdaqNordicequitiesTotalviewGlimpseV3001Server

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

/-- Symbol State: one byte code -/
def SymbolState.codes : List UInt8 :=
  [0x43, 0x50, 0x4F, 0x54, 0x49, 0x4C, 0x53, 0x48, 0x51, 0x41]

inductive SymbolState where
  | closed -- Closed
  | preOpen -- Pre Open
  | openingAuction -- Opening Auction
  | continuousTrading -- Continuous Trading
  | scheduledIntradayAuction -- Scheduled Intraday Auction
  | closingAuction -- Closing Auction
  | postTrade -- Post Trade
  | halted -- Halted
  | auctionPeriod -- Auction Period
  | tradingAtClosingPrice -- Trading At Closing Price
  | unlisted (byte : { byte : UInt8 // byte ∉ SymbolState.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace SymbolState

def toByte : SymbolState → UInt8
  | .closed => 0x43
  | .preOpen => 0x50
  | .openingAuction => 0x4F
  | .continuousTrading => 0x54
  | .scheduledIntradayAuction => 0x49
  | .closingAuction => 0x4C
  | .postTrade => 0x53
  | .halted => 0x48
  | .auctionPeriod => 0x51
  | .tradingAtClosingPrice => 0x41
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : SymbolState :=
  if byte = 0x43 then .closed
  else if byte = 0x50 then .preOpen
  else if byte = 0x4F then .openingAuction
  else if byte = 0x54 then .continuousTrading
  else if byte = 0x49 then .scheduledIntradayAuction
  else if byte = 0x4C then .closingAuction
  else if byte = 0x53 then .postTrade
  else if byte = 0x48 then .halted
  else if byte = 0x51 then .auctionPeriod
  else .tradingAtClosingPrice

def ofByte (byte : UInt8) : SymbolState :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : SymbolState) : ofByte value.toByte = value := by
  cases value with
  | closed => decide
  | preOpen => decide
  | openingAuction => decide
  | continuousTrading => decide
  | scheduledIntradayAuction => decide
  | closingAuction => decide
  | postTrade => decide
  | halted => decide
  | auctionPeriod => decide
  | tradingAtClosingPrice => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : SymbolState) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (SymbolState × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : SymbolState) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : SymbolState) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end SymbolState

/-- Extension: one byte code -/
def Extension.codes : List UInt8 :=
  [0x45]

inductive Extension where
  | crossExtension -- Cross Extension
  | unlisted (byte : { byte : UInt8 // byte ∉ Extension.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace Extension

def toByte : Extension → UInt8
  | .crossExtension => 0x45
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (_ : UInt8) : Extension :=
  .crossExtension

def ofByte (byte : UInt8) : Extension :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : Extension) : ofByte value.toByte = value := by
  cases value with
  | crossExtension => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : Extension) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (Extension × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : Extension) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : Extension) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end Extension

/-- Price Notation: one byte code -/
def PriceNotation.codes : List UInt8 :=
  [0x4D]

inductive PriceNotation where
  | monetaryValue -- Monetary Value
  | unlisted (byte : { byte : UInt8 // byte ∉ PriceNotation.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace PriceNotation

def toByte : PriceNotation → UInt8
  | .monetaryValue => 0x4D
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (_ : UInt8) : PriceNotation :=
  .monetaryValue

def ofByte (byte : UInt8) : PriceNotation :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : PriceNotation) : ofByte value.toByte = value := by
  cases value with
  | monetaryValue => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : PriceNotation) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (PriceNotation × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : PriceNotation) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : PriceNotation) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end PriceNotation

/-- Buy Sell Indicator: one byte code -/
def BuySellIndicator.codes : List UInt8 :=
  [0x42, 0x53]

inductive BuySellIndicator where
  | buyOrder -- Buy Order
  | sellOrder -- Sell Order
  | unlisted (byte : { byte : UInt8 // byte ∉ BuySellIndicator.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace BuySellIndicator

def toByte : BuySellIndicator → UInt8
  | .buyOrder => 0x42
  | .sellOrder => 0x53
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : BuySellIndicator :=
  if byte = 0x42 then .buyOrder
  else .sellOrder

def ofByte (byte : UInt8) : BuySellIndicator :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : BuySellIndicator) : ofByte value.toByte = value := by
  cases value with
  | buyOrder => decide
  | sellOrder => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : BuySellIndicator) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (BuySellIndicator × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : BuySellIndicator) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : BuySellIndicator) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end BuySellIndicator

/-- Debug Packet: 1 bytes -/
structure DebugPacket where
  text : Alpha 1
  deriving DecidableEq, Repr

namespace DebugPacket

def encode (message : DebugPacket) : List UInt8 :=
  Alpha.encode message.text

def decode (bytes : List UInt8) : Option (DebugPacket × List UInt8) := do
  let (text, bytes) ← Alpha.decode 1 bytes
  pure ({ text }, bytes)

@[simp] theorem encode_length (message : DebugPacket) : (encode message).length = 1 := by
  unfold encode
  simp only [Alpha.encode_length]

theorem encode_length_pos (message : DebugPacket) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : DebugPacket) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [Alpha.decode_encode, some_bind]
  rfl

end DebugPacket

/-- Login Accepted Packet: 30 bytes -/
structure LoginAcceptedPacket where
  session : Alpha 10
  sequenceNumber : Alpha 20
  deriving DecidableEq, Repr

namespace LoginAcceptedPacket

def encode (message : LoginAcceptedPacket) : List UInt8 :=
  Alpha.encode message.session
    ++ (Alpha.encode message.sequenceNumber)

def decode (bytes : List UInt8) : Option (LoginAcceptedPacket × List UInt8) := do
  let (session, bytes) ← Alpha.decode 10 bytes
  let (sequenceNumber, bytes) ← Alpha.decode 20 bytes
  pure ({ session, sequenceNumber }, bytes)

@[simp] theorem encode_length (message : LoginAcceptedPacket) : (encode message).length = 30 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length]

theorem encode_length_pos (message : LoginAcceptedPacket) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : LoginAcceptedPacket) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end LoginAcceptedPacket

/-- Login Rejected Packet: 1 bytes -/
structure LoginRejectedPacket where
  rejectReasonCode : Alpha 1
  deriving DecidableEq, Repr

namespace LoginRejectedPacket

def encode (message : LoginRejectedPacket) : List UInt8 :=
  Alpha.encode message.rejectReasonCode

def decode (bytes : List UInt8) : Option (LoginRejectedPacket × List UInt8) := do
  let (rejectReasonCode, bytes) ← Alpha.decode 1 bytes
  pure ({ rejectReasonCode }, bytes)

@[simp] theorem encode_length (message : LoginRejectedPacket) : (encode message).length = 1 := by
  unfold encode
  simp only [Alpha.encode_length]

theorem encode_length_pos (message : LoginRejectedPacket) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : LoginRejectedPacket) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [Alpha.decode_encode, some_bind]
  rfl

end LoginRejectedPacket

/-- System Event Message: 11 bytes -/
structure SystemEventMessage where
  timestamp : BitVec 64
  trackingNumber : BitVec 16
  eventCode : EventCode
  deriving DecidableEq, Repr

namespace SystemEventMessage

def encode (message : SystemEventMessage) : List UInt8 :=
  encodeUInt 8 message.timestamp
    ++ (encodeUInt 2 message.trackingNumber
    ++ (EventCode.encode message.eventCode))

def decode (bytes : List UInt8) : Option (SystemEventMessage × List UInt8) := do
  let (timestamp, bytes) ← decodeUInt 8 bytes
  let (trackingNumber, bytes) ← decodeUInt 2 bytes
  let (eventCode, bytes) ← EventCode.decode bytes
  pure ({ timestamp, trackingNumber, eventCode }, bytes)

@[simp] theorem encode_length (message : SystemEventMessage) : (encode message).length = 11 := by
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
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [EventCode.decode_encode, some_bind]
  rfl

end SystemEventMessage

/-- Order Book Trading Action Message: 20 bytes -/
structure OrderBookTradingActionMessage where
  timestamp : BitVec 64
  trackingNumber : BitVec 16
  orderBook : BitVec 32
  symbolState : SymbolState
  extension : Extension
  reason : Alpha 4
  deriving DecidableEq, Repr

namespace OrderBookTradingActionMessage

def encode (message : OrderBookTradingActionMessage) : List UInt8 :=
  encodeUInt 8 message.timestamp
    ++ (encodeUInt 2 message.trackingNumber
    ++ (encodeUInt 4 message.orderBook
    ++ (SymbolState.encode message.symbolState
    ++ (Extension.encode message.extension
    ++ (Alpha.encode message.reason)))))

def decode (bytes : List UInt8) : Option (OrderBookTradingActionMessage × List UInt8) := do
  let (timestamp, bytes) ← decodeUInt 8 bytes
  let (trackingNumber, bytes) ← decodeUInt 2 bytes
  let (orderBook, bytes) ← decodeUInt 4 bytes
  let (symbolState, bytes) ← SymbolState.decode bytes
  let (extension, bytes) ← Extension.decode bytes
  let (reason, bytes) ← Alpha.decode 4 bytes
  pure ({ timestamp, trackingNumber, orderBook, symbolState, extension, reason }, bytes)

@[simp] theorem encode_length (message : OrderBookTradingActionMessage) : (encode message).length = 20 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, SymbolState.encode_length, Extension.encode_length, Alpha.encode_length]

theorem encode_length_pos (message : OrderBookTradingActionMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OrderBookTradingActionMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, SymbolState.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Extension.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end OrderBookTradingActionMessage

/-- Order Book Directory Message: 96 bytes -/
structure OrderBookDirectoryMessage where
  timestamp : BitVec 64
  trackingNumber : BitVec 16
  orderBook : BitVec 32
  symbol : Alpha 16
  isin : Alpha 12
  financialProduct : BitVec 8
  tradingCurrency : Alpha 3
  mic : Alpha 4
  marketSegmentId : BitVec 16
  noteCodesBitField1 : BitVec 8
  noteCodesBitField2 : BitVec 8
  noteCodesBitField3 : BitVec 8
  noteCodesBitField4 : BitVec 8
  noteCodesBitField5 : BitVec 8
  noteCodesBitField6 : BitVec 8
  noteCodesBitField7 : BitVec 8
  noteCodesBitField8 : BitVec 8
  roundLotSize : BitVec 32
  nordicMidMic : Alpha 4
  aodMic : Alpha 4
  notationOfQty : Alpha 4
  notionalAmount : BitVec 64
  currency : Alpha 3
  priceNotation : PriceNotation
  multiplierForCalculatingQuantityInMeasurementUnit : BitVec 64
  deriving DecidableEq, Repr

namespace OrderBookDirectoryMessage

def encode (message : OrderBookDirectoryMessage) : List UInt8 :=
  encodeUInt 8 message.timestamp
    ++ (encodeUInt 2 message.trackingNumber
    ++ (encodeUInt 4 message.orderBook
    ++ (Alpha.encode message.symbol
    ++ (Alpha.encode message.isin
    ++ (encodeUInt 1 message.financialProduct
    ++ (Alpha.encode message.tradingCurrency
    ++ (Alpha.encode message.mic
    ++ (encodeUInt 2 message.marketSegmentId
    ++ (encodeUIntLE 1 message.noteCodesBitField1
    ++ (encodeUIntLE 1 message.noteCodesBitField2
    ++ (encodeUIntLE 1 message.noteCodesBitField3
    ++ (encodeUIntLE 1 message.noteCodesBitField4
    ++ (encodeUIntLE 1 message.noteCodesBitField5
    ++ (encodeUIntLE 1 message.noteCodesBitField6
    ++ (encodeUIntLE 1 message.noteCodesBitField7
    ++ (encodeUIntLE 1 message.noteCodesBitField8
    ++ (encodeUInt 4 message.roundLotSize
    ++ (Alpha.encode message.nordicMidMic
    ++ (Alpha.encode message.aodMic
    ++ (Alpha.encode message.notationOfQty
    ++ (encodeUInt 8 message.notionalAmount
    ++ (Alpha.encode message.currency
    ++ (PriceNotation.encode message.priceNotation
    ++ (encodeUInt 8 message.multiplierForCalculatingQuantityInMeasurementUnit))))))))))))))))))))))))

-- a long run of fields nests deeper than the elaborator's default limit
set_option maxRecDepth 4096 in
def decode (bytes : List UInt8) : Option (OrderBookDirectoryMessage × List UInt8) := do
  let (timestamp, bytes) ← decodeUInt 8 bytes
  let (trackingNumber, bytes) ← decodeUInt 2 bytes
  let (orderBook, bytes) ← decodeUInt 4 bytes
  let (symbol, bytes) ← Alpha.decode 16 bytes
  let (isin, bytes) ← Alpha.decode 12 bytes
  let (financialProduct, bytes) ← decodeUInt 1 bytes
  let (tradingCurrency, bytes) ← Alpha.decode 3 bytes
  let (mic, bytes) ← Alpha.decode 4 bytes
  let (marketSegmentId, bytes) ← decodeUInt 2 bytes
  let (noteCodesBitField1, bytes) ← decodeUIntLE 1 bytes
  let (noteCodesBitField2, bytes) ← decodeUIntLE 1 bytes
  let (noteCodesBitField3, bytes) ← decodeUIntLE 1 bytes
  let (noteCodesBitField4, bytes) ← decodeUIntLE 1 bytes
  let (noteCodesBitField5, bytes) ← decodeUIntLE 1 bytes
  let (noteCodesBitField6, bytes) ← decodeUIntLE 1 bytes
  let (noteCodesBitField7, bytes) ← decodeUIntLE 1 bytes
  let (noteCodesBitField8, bytes) ← decodeUIntLE 1 bytes
  let (roundLotSize, bytes) ← decodeUInt 4 bytes
  let (nordicMidMic, bytes) ← Alpha.decode 4 bytes
  let (aodMic, bytes) ← Alpha.decode 4 bytes
  let (notationOfQty, bytes) ← Alpha.decode 4 bytes
  let (notionalAmount, bytes) ← decodeUInt 8 bytes
  let (currency, bytes) ← Alpha.decode 3 bytes
  let (priceNotation, bytes) ← PriceNotation.decode bytes
  let (multiplierForCalculatingQuantityInMeasurementUnit, bytes) ← decodeUInt 8 bytes
  pure ({ timestamp, trackingNumber, orderBook, symbol, isin, financialProduct, tradingCurrency, mic, marketSegmentId, noteCodesBitField1, noteCodesBitField2, noteCodesBitField3, noteCodesBitField4, noteCodesBitField5, noteCodesBitField6, noteCodesBitField7, noteCodesBitField8, roundLotSize, nordicMidMic, aodMic, notationOfQty, notionalAmount, currency, priceNotation, multiplierForCalculatingQuantityInMeasurementUnit }, bytes)

@[simp] theorem encode_length (message : OrderBookDirectoryMessage) : (encode message).length = 96 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Alpha.encode_length, encodeUIntLE_length, PriceNotation.encode_length]

theorem encode_length_pos (message : OrderBookDirectoryMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

set_option maxRecDepth 4096 in
@[simp] theorem decode_encode (message : OrderBookDirectoryMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
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
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
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
  rw [List.append_assoc, PriceNotation.decode_encode, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end OrderBookDirectoryMessage

/-- Add Order Message: 31 bytes -/
structure AddOrderMessage where
  timestamp : BitVec 64
  trackingNumber : BitVec 16
  orderReferenceNumber : BitVec 64
  buySellIndicator : BuySellIndicator
  quantity : BitVec 32
  orderBook : BitVec 32
  price : BitVec 32
  deriving DecidableEq, Repr

namespace AddOrderMessage

def encode (message : AddOrderMessage) : List UInt8 :=
  encodeUInt 8 message.timestamp
    ++ (encodeUInt 2 message.trackingNumber
    ++ (encodeUInt 8 message.orderReferenceNumber
    ++ (BuySellIndicator.encode message.buySellIndicator
    ++ (encodeUInt 4 message.quantity
    ++ (encodeUInt 4 message.orderBook
    ++ (encodeUInt 4 message.price))))))

def decode (bytes : List UInt8) : Option (AddOrderMessage × List UInt8) := do
  let (timestamp, bytes) ← decodeUInt 8 bytes
  let (trackingNumber, bytes) ← decodeUInt 2 bytes
  let (orderReferenceNumber, bytes) ← decodeUInt 8 bytes
  let (buySellIndicator, bytes) ← BuySellIndicator.decode bytes
  let (quantity, bytes) ← decodeUInt 4 bytes
  let (orderBook, bytes) ← decodeUInt 4 bytes
  let (price, bytes) ← decodeUInt 4 bytes
  pure ({ timestamp, trackingNumber, orderReferenceNumber, buySellIndicator, quantity, orderBook, price }, bytes)

@[simp] theorem encode_length (message : AddOrderMessage) : (encode message).length = 31 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, BuySellIndicator.encode_length]

theorem encode_length_pos (message : AddOrderMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : AddOrderMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, BuySellIndicator.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end AddOrderMessage

/-- Add Order Mpid Attribution Message: 35 bytes -/
structure AddOrderMpidAttributionMessage where
  timestamp : BitVec 64
  trackingNumber : BitVec 16
  orderReferenceNumber : BitVec 64
  buySellIndicator : BuySellIndicator
  quantity : BitVec 32
  orderBook : BitVec 32
  price : BitVec 32
  attribution : Alpha 4
  deriving DecidableEq, Repr

namespace AddOrderMpidAttributionMessage

def encode (message : AddOrderMpidAttributionMessage) : List UInt8 :=
  encodeUInt 8 message.timestamp
    ++ (encodeUInt 2 message.trackingNumber
    ++ (encodeUInt 8 message.orderReferenceNumber
    ++ (BuySellIndicator.encode message.buySellIndicator
    ++ (encodeUInt 4 message.quantity
    ++ (encodeUInt 4 message.orderBook
    ++ (encodeUInt 4 message.price
    ++ (Alpha.encode message.attribution)))))))

def decode (bytes : List UInt8) : Option (AddOrderMpidAttributionMessage × List UInt8) := do
  let (timestamp, bytes) ← decodeUInt 8 bytes
  let (trackingNumber, bytes) ← decodeUInt 2 bytes
  let (orderReferenceNumber, bytes) ← decodeUInt 8 bytes
  let (buySellIndicator, bytes) ← BuySellIndicator.decode bytes
  let (quantity, bytes) ← decodeUInt 4 bytes
  let (orderBook, bytes) ← decodeUInt 4 bytes
  let (price, bytes) ← decodeUInt 4 bytes
  let (attribution, bytes) ← Alpha.decode 4 bytes
  pure ({ timestamp, trackingNumber, orderReferenceNumber, buySellIndicator, quantity, orderBook, price, attribution }, bytes)

@[simp] theorem encode_length (message : AddOrderMpidAttributionMessage) : (encode message).length = 35 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, BuySellIndicator.encode_length, Alpha.encode_length]

theorem encode_length_pos (message : AddOrderMpidAttributionMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : AddOrderMpidAttributionMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, BuySellIndicator.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end AddOrderMpidAttributionMessage

/-- End Of Snapshot Message: 20 bytes -/
structure EndOfSnapshotMessage where
  sequenceNumber : Alpha 20
  deriving DecidableEq, Repr

namespace EndOfSnapshotMessage

def encode (message : EndOfSnapshotMessage) : List UInt8 :=
  Alpha.encode message.sequenceNumber

def decode (bytes : List UInt8) : Option (EndOfSnapshotMessage × List UInt8) := do
  let (sequenceNumber, bytes) ← Alpha.decode 20 bytes
  pure ({ sequenceNumber }, bytes)

@[simp] theorem encode_length (message : EndOfSnapshotMessage) : (encode message).length = 20 := by
  unfold encode
  simp only [Alpha.encode_length]

theorem encode_length_pos (message : EndOfSnapshotMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : EndOfSnapshotMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [Alpha.decode_encode, some_bind]
  rfl

end EndOfSnapshotMessage

/-- Any Sequenced Message, selected by Sequenced Message Type -/
inductive SequencedMessage where
  | systemEventMessage (message : SystemEventMessage) -- 'S' 0x53
  | orderBookTradingActionMessage (message : OrderBookTradingActionMessage) -- 'H' 0x48
  | orderBookDirectoryMessage (message : OrderBookDirectoryMessage) -- 'R' 0x52
  | addOrderMessage (message : AddOrderMessage) -- 'A' 0x41
  | addOrderMpidAttributionMessage (message : AddOrderMpidAttributionMessage) -- 'F' 0x46
  | endOfSnapshotMessage (message : EndOfSnapshotMessage) -- 'G' 0x47
  deriving DecidableEq, Repr

namespace SequencedMessage

/-- The Sequenced Message Type each message is sent under -/
def tag : SequencedMessage → BitVec 8
  | .systemEventMessage _ => 83
  | .orderBookTradingActionMessage _ => 72
  | .orderBookDirectoryMessage _ => 82
  | .addOrderMessage _ => 65
  | .addOrderMpidAttributionMessage _ => 70
  | .endOfSnapshotMessage _ => 71

def encode : SequencedMessage → List UInt8
  | .systemEventMessage message => SystemEventMessage.encode message
  | .orderBookTradingActionMessage message => OrderBookTradingActionMessage.encode message
  | .orderBookDirectoryMessage message => OrderBookDirectoryMessage.encode message
  | .addOrderMessage message => AddOrderMessage.encode message
  | .addOrderMpidAttributionMessage message => AddOrderMpidAttributionMessage.encode message
  | .endOfSnapshotMessage message => EndOfSnapshotMessage.encode message

/-- The most bytes any message's encoding can take -/
theorem encode_length_le (message : SequencedMessage) : (encode message).length ≤ 96 := by
  cases message with
  | systemEventMessage inner =>
    simp only [encode, SystemEventMessage.encode_length]
    omega
  | orderBookTradingActionMessage inner =>
    simp only [encode, OrderBookTradingActionMessage.encode_length]
    omega
  | orderBookDirectoryMessage inner =>
    simp only [encode, OrderBookDirectoryMessage.encode_length]
    omega
  | addOrderMessage inner =>
    simp only [encode, AddOrderMessage.encode_length]
    omega
  | addOrderMpidAttributionMessage inner =>
    simp only [encode, AddOrderMpidAttributionMessage.encode_length]
    omega
  | endOfSnapshotMessage inner =>
    simp only [encode, EndOfSnapshotMessage.encode_length]
    omega

def decode (tag : BitVec 8) (bytes : List UInt8) : Option (SequencedMessage × List UInt8) :=
  if tag = 83 then (SystemEventMessage.decode bytes).map fun (message, rest) => (.systemEventMessage message, rest)
  else if tag = 72 then (OrderBookTradingActionMessage.decode bytes).map fun (message, rest) => (.orderBookTradingActionMessage message, rest)
  else if tag = 82 then (OrderBookDirectoryMessage.decode bytes).map fun (message, rest) => (.orderBookDirectoryMessage message, rest)
  else if tag = 65 then (AddOrderMessage.decode bytes).map fun (message, rest) => (.addOrderMessage message, rest)
  else if tag = 70 then (AddOrderMpidAttributionMessage.decode bytes).map fun (message, rest) => (.addOrderMpidAttributionMessage message, rest)
  else if tag = 71 then (EndOfSnapshotMessage.decode bytes).map fun (message, rest) => (.endOfSnapshotMessage message, rest)
  else none

@[simp] theorem decode_encode (message : SequencedMessage) (rest : List UInt8) :
    decode (tag message) (encode message ++ rest) = some (message, rest) := by
  cases message <;> simp [decode, encode, tag]

end SequencedMessage

/-- Sequenced Data Packet -/
structure SequencedDataPacket where
  sequencedMessage : SequencedMessage
  deriving DecidableEq, Repr

namespace SequencedDataPacket

def encode (message : SequencedDataPacket) : List UInt8 :=
  encodeUInt 1 (SequencedMessage.tag message.sequencedMessage)
    ++ (SequencedMessage.encode message.sequencedMessage)

def decode (bytes : List UInt8) : Option (SequencedDataPacket × List UInt8) := do
  let (sequencedMessageType, bytes) ← decodeUInt 1 bytes
  let (sequencedMessage, bytes) ← SequencedMessage.decode sequencedMessageType bytes
  pure ({ sequencedMessage }, bytes)

theorem encode_length_pos (message : SequencedDataPacket) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUInt_length, List.length_append]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : SequencedDataPacket) : (encode message).length ≤ 97 := by
  unfold encode
  cases message.sequencedMessage with
  | systemEventMessage inner =>
    simp only [SequencedMessage.encode, List.length_append, encodeUInt_length, SystemEventMessage.encode_length]
    omega
  | orderBookTradingActionMessage inner =>
    simp only [SequencedMessage.encode, List.length_append, encodeUInt_length, OrderBookTradingActionMessage.encode_length]
    omega
  | orderBookDirectoryMessage inner =>
    simp only [SequencedMessage.encode, List.length_append, encodeUInt_length, OrderBookDirectoryMessage.encode_length]
    omega
  | addOrderMessage inner =>
    simp only [SequencedMessage.encode, List.length_append, encodeUInt_length, AddOrderMessage.encode_length]
    omega
  | addOrderMpidAttributionMessage inner =>
    simp only [SequencedMessage.encode, List.length_append, encodeUInt_length, AddOrderMpidAttributionMessage.encode_length]
    omega
  | endOfSnapshotMessage inner =>
    simp only [SequencedMessage.encode, List.length_append, encodeUInt_length, EndOfSnapshotMessage.encode_length]
    omega

@[simp] theorem decode_encode (message : SequencedDataPacket) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [SequencedMessage.decode_encode, some_bind]
  rfl

end SequencedDataPacket

/-- Server Heartbeat: 0 bytes -/
structure ServerHeartbeat where
  deriving DecidableEq, Repr

namespace ServerHeartbeat

def encode (_ : ServerHeartbeat) : List UInt8 :=
  []

def decode (bytes : List UInt8) : Option (ServerHeartbeat × List UInt8) :=
  some (⟨⟩, bytes)

@[simp] theorem encode_length (message : ServerHeartbeat) : (encode message).length = 0 := by
  simp [encode]

@[simp] theorem decode_encode (message : ServerHeartbeat) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  simp [decode, encode]

end ServerHeartbeat

/-- End Of Session: 0 bytes -/
structure EndOfSession where
  deriving DecidableEq, Repr

namespace EndOfSession

def encode (_ : EndOfSession) : List UInt8 :=
  []

def decode (bytes : List UInt8) : Option (EndOfSession × List UInt8) :=
  some (⟨⟩, bytes)

@[simp] theorem encode_length (message : EndOfSession) : (encode message).length = 0 := by
  simp [encode]

@[simp] theorem decode_encode (message : EndOfSession) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  simp [decode, encode]

end EndOfSession

/-- Any Server Payload, selected by Server Packet Type -/
inductive ServerPayload where
  | debugPacket (message : DebugPacket) -- '+' 0x2B
  | loginAcceptedPacket (message : LoginAcceptedPacket) -- 'A' 0x41
  | loginRejectedPacket (message : LoginRejectedPacket) -- 'J' 0x4A
  | sequencedDataPacket (message : SequencedDataPacket) -- 'S' 0x53
  | serverHeartbeat (message : ServerHeartbeat) -- 'H' 0x48
  | endOfSession (message : EndOfSession) -- 'Z' 0x5A
  deriving DecidableEq, Repr

namespace ServerPayload

/-- The Server Packet Type each message is sent under -/
def tag : ServerPayload → BitVec 8
  | .debugPacket _ => 43
  | .loginAcceptedPacket _ => 65
  | .loginRejectedPacket _ => 74
  | .sequencedDataPacket _ => 83
  | .serverHeartbeat _ => 72
  | .endOfSession _ => 90

def encode : ServerPayload → List UInt8
  | .debugPacket message => DebugPacket.encode message
  | .loginAcceptedPacket message => LoginAcceptedPacket.encode message
  | .loginRejectedPacket message => LoginRejectedPacket.encode message
  | .sequencedDataPacket message => SequencedDataPacket.encode message
  | .serverHeartbeat message => ServerHeartbeat.encode message
  | .endOfSession message => EndOfSession.encode message

/-- The most bytes any message's encoding can take -/
theorem encode_length_le (message : ServerPayload) : (encode message).length ≤ 97 := by
  cases message with
  | debugPacket inner =>
    simp only [encode, DebugPacket.encode_length]
    omega
  | loginAcceptedPacket inner =>
    simp only [encode, LoginAcceptedPacket.encode_length]
    omega
  | loginRejectedPacket inner =>
    simp only [encode, LoginRejectedPacket.encode_length]
    omega
  | sequencedDataPacket inner =>
    have bound_inner := SequencedDataPacket.encode_length_le inner
    simp only [encode]
    omega
  | serverHeartbeat inner =>
    simp only [encode, ServerHeartbeat.encode_length]
    omega
  | endOfSession inner =>
    simp only [encode, EndOfSession.encode_length]
    omega

def decode (tag : BitVec 8) (bytes : List UInt8) : Option (ServerPayload × List UInt8) :=
  if tag = 43 then (DebugPacket.decode bytes).map fun (message, rest) => (.debugPacket message, rest)
  else if tag = 65 then (LoginAcceptedPacket.decode bytes).map fun (message, rest) => (.loginAcceptedPacket message, rest)
  else if tag = 74 then (LoginRejectedPacket.decode bytes).map fun (message, rest) => (.loginRejectedPacket message, rest)
  else if tag = 83 then (SequencedDataPacket.decode bytes).map fun (message, rest) => (.sequencedDataPacket message, rest)
  else if tag = 72 then (ServerHeartbeat.decode bytes).map fun (message, rest) => (.serverHeartbeat message, rest)
  else if tag = 90 then (EndOfSession.decode bytes).map fun (message, rest) => (.endOfSession message, rest)
  else none

@[simp] theorem decode_encode (message : ServerPayload) (rest : List UInt8) :
    decode (tag message) (encode message ++ rest) = some (message, rest) := by
  cases message <;> simp [decode, encode, tag]

end ServerPayload

/-- Server Soup Bin Tcp Packet -/
structure ServerSoupBinTcpPacket where
  serverPayload : ServerPayload
  deriving DecidableEq, Repr

namespace ServerSoupBinTcpPacket

def encodeBody (message : ServerSoupBinTcpPacket) : List UInt8 :=
  encodeUInt 1 (ServerPayload.tag message.serverPayload)
    ++ (ServerPayload.encode message.serverPayload)

def decodeBody (bytes : List UInt8) : Option (ServerSoupBinTcpPacket × List UInt8) := do
  let (serverPacketType, bytes) ← decodeUInt 1 bytes
  let (serverPayload, bytes) ← ServerPayload.decode serverPacketType bytes
  pure ({ serverPayload }, bytes)

theorem decodeBody_encodeBody (message : ServerSoupBinTcpPacket) (rest : List UInt8) :
    decodeBody (encodeBody message ++ rest) = some (message, rest) := by
  unfold decodeBody encodeBody
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [ServerPayload.decode_encode, some_bind]
  rfl

/-- Every body fits the length prefix -/
theorem encodeBody_length_lt (message : ServerSoupBinTcpPacket) : (encodeBody message).length + 0 < 256 ^ 2 := by
  unfold encodeBody
  cases message.serverPayload with
  | debugPacket inner =>
    simp only [ServerPayload.encode, List.length_append, encodeUInt_length, DebugPacket.encode_length]
    omega
  | loginAcceptedPacket inner =>
    simp only [ServerPayload.encode, List.length_append, encodeUInt_length, LoginAcceptedPacket.encode_length]
    omega
  | loginRejectedPacket inner =>
    simp only [ServerPayload.encode, List.length_append, encodeUInt_length, LoginRejectedPacket.encode_length]
    omega
  | sequencedDataPacket inner =>
    have bound_inner := SequencedDataPacket.encode_length_le inner
    simp only [ServerPayload.encode, List.length_append, encodeUInt_length]
    omega
  | serverHeartbeat inner =>
    simp only [ServerPayload.encode, List.length_append, encodeUInt_length, ServerHeartbeat.encode_length]
    omega
  | endOfSession inner =>
    simp only [ServerPayload.encode, List.length_append, encodeUInt_length, EndOfSession.encode_length]
    omega

/-- Size rule: Packet Length counts the bytes after it, so it is written from the body and checked on decode -/
def encode : ServerSoupBinTcpPacket → List UInt8 :=
  encodeFramed 2 0 encodeBody

def decode : List UInt8 → Option (ServerSoupBinTcpPacket × List UInt8) :=
  decodeFramed 2 0 decodeBody

@[simp] theorem decode_encode (message : ServerSoupBinTcpPacket) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) :=
  decodeFramed_encodeFramed 2 0 encodeBody decodeBody message (decodeBody_encodeBody message) (encodeBody_length_lt message) rest

theorem encode_length_pos (message : ServerSoupBinTcpPacket) : (encode message).length > 0 := by
  unfold encode
  rw [encodeFramed_length]
  omega

end ServerSoupBinTcpPacket

/-- Server Packet -/
structure ServerPacket where
  serverSoupBinTcpPacket : List ServerSoupBinTcpPacket
  deriving DecidableEq, Repr

namespace ServerPacket

def encode (message : ServerPacket) : List UInt8 :=
  encodeMany ServerSoupBinTcpPacket.encode message.serverSoupBinTcpPacket

def decode (bytes : List UInt8) : Option ServerPacket := do
  let serverSoupBinTcpPacket ← decodeAll ServerSoupBinTcpPacket.decode bytes.length bytes
  pure { serverSoupBinTcpPacket }

theorem decode_encode (message : ServerPacket) : decode (encode message) = some message := by
  unfold decode encode
  rw [decodeAll_encodeMany ServerSoupBinTcpPacket.encode ServerSoupBinTcpPacket.decode ServerSoupBinTcpPacket.decode_encode ServerSoupBinTcpPacket.encode_length_pos message.serverSoupBinTcpPacket _ (encodeMany_length_ge ServerSoupBinTcpPacket.encode ServerSoupBinTcpPacket.encode_length_pos message.serverSoupBinTcpPacket), some_bind]
  rfl

end ServerPacket

end Omi.NasdaqNordicequitiesTotalviewGlimpseV3001Server
