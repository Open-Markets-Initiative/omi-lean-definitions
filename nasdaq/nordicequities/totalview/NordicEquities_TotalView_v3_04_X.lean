import Omi.Wire

/-!
# National Association of Securities Dealers Automated Quotations (Nasdaq) Nordic Equity TotalView v3.04.X

Generated from the binary model, with the proofs the model's rules call for: every record
decodes back to what was encoded; a message dispatch selects the message its type names;
a count is written from the list it counts; a length prefix is written from the bytes it frames;
and a packet read to the end of its data decodes to the messages that were written.

Note: a Message Count of 0 marks Heartbeat and carries no messages; the decoder reads it as a count and the encoder never writes it.

Note: a Message Count of 65535 marks End Of Session and carries no messages; the decoder reads it as a count and the encoder never writes it.

Note: Note Codes Bit Field 1 is a bit field set, proven as its 1 byte integer rather than bit by bit.

Note: Note Codes Bit Field 2 is a bit field set, proven as its 1 byte integer rather than bit by bit.

Note: Note Codes Bit Field 3 is a bit field set, proven as its 1 byte integer rather than bit by bit.

Note: Note Codes Bit Field 4 is a bit field set, proven as its 1 byte integer rather than bit by bit.

Note: Note Codes Bit Field 5 is a bit field set, proven as its 1 byte integer rather than bit by bit.

Note: Note Codes Bit Field 6 is a bit field set, proven as its 1 byte integer rather than bit by bit.

Note: Note Codes Bit Field 7 is a bit field set, proven as its 1 byte integer rather than bit by bit.

Note: Note Codes Bit Field 8 is a bit field set, proven as its 1 byte integer rather than bit by bit.

Text fields are kept byte for byte, padding included, so what is decoded encodes back unchanged.
Prices with implied decimals are proven as the integers on the wire.
-/

namespace Omi.NasdaqNordicequitiesTotalviewItchV304X

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

/-- Trade Type: one byte code -/
def TradeType.codes : List UInt8 :=
  [0x42, 0x53]

inductive TradeType where
  | mainBook -- Main Book
  | nordicMid -- Nordic Mid
  | unlisted (byte : { byte : UInt8 // byte ∉ TradeType.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace TradeType

def toByte : TradeType → UInt8
  | .mainBook => 0x42
  | .nordicMid => 0x53
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : TradeType :=
  if byte = 0x42 then .mainBook
  else .nordicMid

def ofByte (byte : UInt8) : TradeType :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : TradeType) : ofByte value.toByte = value := by
  cases value with
  | mainBook => decide
  | nordicMid => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : TradeType) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (TradeType × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : TradeType) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : TradeType) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end TradeType

/-- Cross Type: one byte code -/
def CrossType.codes : List UInt8 :=
  [0x4F, 0x49, 0x43, 0x48, 0x41]

inductive CrossType where
  | openingCross -- Opening Cross
  | scheduledIntradayCross -- Scheduled Intraday Cross
  | closingCross -- Closing Cross
  | crossForHaltedSecurities -- Cross For Halted Securities
  | auctionOnDemand -- Auction On Demand
  | unlisted (byte : { byte : UInt8 // byte ∉ CrossType.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace CrossType

def toByte : CrossType → UInt8
  | .openingCross => 0x4F
  | .scheduledIntradayCross => 0x49
  | .closingCross => 0x43
  | .crossForHaltedSecurities => 0x48
  | .auctionOnDemand => 0x41
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : CrossType :=
  if byte = 0x4F then .openingCross
  else if byte = 0x49 then .scheduledIntradayCross
  else if byte = 0x43 then .closingCross
  else if byte = 0x48 then .crossForHaltedSecurities
  else .auctionOnDemand

def ofByte (byte : UInt8) : CrossType :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : CrossType) : ofByte value.toByte = value := by
  cases value with
  | openingCross => decide
  | scheduledIntradayCross => decide
  | closingCross => decide
  | crossForHaltedSecurities => decide
  | auctionOnDemand => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : CrossType) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (CrossType × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : CrossType) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : CrossType) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end CrossType

/-- Imbalance Direction: one byte code -/
def ImbalanceDirection.codes : List UInt8 :=
  [0x42, 0x53, 0x4E, 0x4F]

inductive ImbalanceDirection where
  | buyImbalance -- Buy Imbalance
  | sellImbalance -- Sell Imbalance
  | noImbalance -- No Imbalance
  | insufficientOrdersToCalculate -- Insufficient Orders To Calculate
  | unlisted (byte : { byte : UInt8 // byte ∉ ImbalanceDirection.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace ImbalanceDirection

def toByte : ImbalanceDirection → UInt8
  | .buyImbalance => 0x42
  | .sellImbalance => 0x53
  | .noImbalance => 0x4E
  | .insufficientOrdersToCalculate => 0x4F
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : ImbalanceDirection :=
  if byte = 0x42 then .buyImbalance
  else if byte = 0x53 then .sellImbalance
  else if byte = 0x4E then .noImbalance
  else .insufficientOrdersToCalculate

def ofByte (byte : UInt8) : ImbalanceDirection :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : ImbalanceDirection) : ofByte value.toByte = value := by
  cases value with
  | buyImbalance => decide
  | sellImbalance => decide
  | noImbalance => decide
  | insufficientOrdersToCalculate => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : ImbalanceDirection) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (ImbalanceDirection × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : ImbalanceDirection) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : ImbalanceDirection) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end ImbalanceDirection

/-- Cross Level: one byte code -/
def CrossLevel.codes : List UInt8 :=
  [0x42, 0x53, 0x4D, 0x4C]

inductive CrossLevel where
  | buy -- Buy
  | sell -- Sell
  | mid -- Mid
  | limit -- Limit
  | unlisted (byte : { byte : UInt8 // byte ∉ CrossLevel.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace CrossLevel

def toByte : CrossLevel → UInt8
  | .buy => 0x42
  | .sell => 0x53
  | .mid => 0x4D
  | .limit => 0x4C
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : CrossLevel :=
  if byte = 0x42 then .buy
  else if byte = 0x53 then .sell
  else if byte = 0x4D then .mid
  else .limit

def ofByte (byte : UInt8) : CrossLevel :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : CrossLevel) : ofByte value.toByte = value := by
  cases value with
  | buy => decide
  | sell => decide
  | mid => decide
  | limit => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : CrossLevel) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (CrossLevel × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : CrossLevel) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : CrossLevel) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end CrossLevel

/-- Aggressing Side: one byte code -/
def AggressingSide.codes : List UInt8 :=
  [0x42, 0x53, 0x20]

inductive AggressingSide where
  | buy -- Buy
  | sell -- Sell
  | none_ -- None
  | unlisted (byte : { byte : UInt8 // byte ∉ AggressingSide.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace AggressingSide

def toByte : AggressingSide → UInt8
  | .buy => 0x42
  | .sell => 0x53
  | .none_ => 0x20
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : AggressingSide :=
  if byte = 0x42 then .buy
  else if byte = 0x53 then .sell
  else .none_

def ofByte (byte : UInt8) : AggressingSide :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : AggressingSide) : ofByte value.toByte = value := by
  cases value with
  | buy => decide
  | sell => decide
  | none_ => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : AggressingSide) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (AggressingSide × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : AggressingSide) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : AggressingSide) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end AggressingSide

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

/-- Order Book Directory Message: 100 bytes -/
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
  pureStreamMic : Alpha 4
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
    ++ (encodeUInt 8 message.multiplierForCalculatingQuantityInMeasurementUnit
    ++ (Alpha.encode message.pureStreamMic)))))))))))))))))))))))))

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
  let (pureStreamMic, bytes) ← Alpha.decode 4 bytes
  pure ({ timestamp, trackingNumber, orderBook, symbol, isin, financialProduct, tradingCurrency, mic, marketSegmentId, noteCodesBitField1, noteCodesBitField2, noteCodesBitField3, noteCodesBitField4, noteCodesBitField5, noteCodesBitField6, noteCodesBitField7, noteCodesBitField8, roundLotSize, nordicMidMic, aodMic, notationOfQty, notionalAmount, currency, priceNotation, multiplierForCalculatingQuantityInMeasurementUnit, pureStreamMic }, bytes)

@[simp] theorem encode_length (message : OrderBookDirectoryMessage) : (encode message).length = 100 := by
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
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
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

/-- Order Executed Message: 34 bytes -/
structure OrderExecutedMessage where
  timestamp : BitVec 64
  trackingNumber : BitVec 16
  orderReferenceNumber : BitVec 64
  executedQuantity : BitVec 32
  matchNumber : BitVec 32
  mpid : Alpha 4
  mpidCounterparty : Alpha 4
  deriving DecidableEq, Repr

namespace OrderExecutedMessage

def encode (message : OrderExecutedMessage) : List UInt8 :=
  encodeUInt 8 message.timestamp
    ++ (encodeUInt 2 message.trackingNumber
    ++ (encodeUInt 8 message.orderReferenceNumber
    ++ (encodeUInt 4 message.executedQuantity
    ++ (encodeUInt 4 message.matchNumber
    ++ (Alpha.encode message.mpid
    ++ (Alpha.encode message.mpidCounterparty))))))

def decode (bytes : List UInt8) : Option (OrderExecutedMessage × List UInt8) := do
  let (timestamp, bytes) ← decodeUInt 8 bytes
  let (trackingNumber, bytes) ← decodeUInt 2 bytes
  let (orderReferenceNumber, bytes) ← decodeUInt 8 bytes
  let (executedQuantity, bytes) ← decodeUInt 4 bytes
  let (matchNumber, bytes) ← decodeUInt 4 bytes
  let (mpid, bytes) ← Alpha.decode 4 bytes
  let (mpidCounterparty, bytes) ← Alpha.decode 4 bytes
  pure ({ timestamp, trackingNumber, orderReferenceNumber, executedQuantity, matchNumber, mpid, mpidCounterparty }, bytes)

@[simp] theorem encode_length (message : OrderExecutedMessage) : (encode message).length = 34 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Alpha.encode_length]

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
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end OrderExecutedMessage

/-- Order Executed With Price Message: 39 bytes -/
structure OrderExecutedWithPriceMessage where
  timestamp : BitVec 64
  trackingNumber : BitVec 16
  orderReferenceNumber : BitVec 64
  executedQuantity : BitVec 32
  matchNumber : BitVec 32
  printable : Printable
  tradePrice : BitVec 32
  mpidOwner : Alpha 4
  mpidCounterparty : Alpha 4
  deriving DecidableEq, Repr

namespace OrderExecutedWithPriceMessage

def encode (message : OrderExecutedWithPriceMessage) : List UInt8 :=
  encodeUInt 8 message.timestamp
    ++ (encodeUInt 2 message.trackingNumber
    ++ (encodeUInt 8 message.orderReferenceNumber
    ++ (encodeUInt 4 message.executedQuantity
    ++ (encodeUInt 4 message.matchNumber
    ++ (Printable.encode message.printable
    ++ (encodeUInt 4 message.tradePrice
    ++ (Alpha.encode message.mpidOwner
    ++ (Alpha.encode message.mpidCounterparty))))))))

def decode (bytes : List UInt8) : Option (OrderExecutedWithPriceMessage × List UInt8) := do
  let (timestamp, bytes) ← decodeUInt 8 bytes
  let (trackingNumber, bytes) ← decodeUInt 2 bytes
  let (orderReferenceNumber, bytes) ← decodeUInt 8 bytes
  let (executedQuantity, bytes) ← decodeUInt 4 bytes
  let (matchNumber, bytes) ← decodeUInt 4 bytes
  let (printable_, bytes) ← Printable.decode bytes
  let (tradePrice, bytes) ← decodeUInt 4 bytes
  let (mpidOwner, bytes) ← Alpha.decode 4 bytes
  let (mpidCounterparty, bytes) ← Alpha.decode 4 bytes
  pure ({ timestamp, trackingNumber, orderReferenceNumber, executedQuantity, matchNumber, printable := printable_, tradePrice, mpidOwner, mpidCounterparty }, bytes)

@[simp] theorem encode_length (message : OrderExecutedWithPriceMessage) : (encode message).length = 39 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Printable.encode_length, Alpha.encode_length]

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
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Printable.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end OrderExecutedWithPriceMessage

/-- Order Cancel Message: 22 bytes -/
structure OrderCancelMessage where
  timestamp : BitVec 64
  trackingNumber : BitVec 16
  orderReferenceNumber : BitVec 64
  canceledQuantity : BitVec 32
  deriving DecidableEq, Repr

namespace OrderCancelMessage

def encode (message : OrderCancelMessage) : List UInt8 :=
  encodeUInt 8 message.timestamp
    ++ (encodeUInt 2 message.trackingNumber
    ++ (encodeUInt 8 message.orderReferenceNumber
    ++ (encodeUInt 4 message.canceledQuantity)))

def decode (bytes : List UInt8) : Option (OrderCancelMessage × List UInt8) := do
  let (timestamp, bytes) ← decodeUInt 8 bytes
  let (trackingNumber, bytes) ← decodeUInt 2 bytes
  let (orderReferenceNumber, bytes) ← decodeUInt 8 bytes
  let (canceledQuantity, bytes) ← decodeUInt 4 bytes
  pure ({ timestamp, trackingNumber, orderReferenceNumber, canceledQuantity }, bytes)

@[simp] theorem encode_length (message : OrderCancelMessage) : (encode message).length = 22 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length]

theorem encode_length_pos (message : OrderCancelMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OrderCancelMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end OrderCancelMessage

/-- Order Delete Message: 18 bytes -/
structure OrderDeleteMessage where
  timestamp : BitVec 64
  trackingNumber : BitVec 16
  orderReferenceNumber : BitVec 64
  deriving DecidableEq, Repr

namespace OrderDeleteMessage

def encode (message : OrderDeleteMessage) : List UInt8 :=
  encodeUInt 8 message.timestamp
    ++ (encodeUInt 2 message.trackingNumber
    ++ (encodeUInt 8 message.orderReferenceNumber))

def decode (bytes : List UInt8) : Option (OrderDeleteMessage × List UInt8) := do
  let (timestamp, bytes) ← decodeUInt 8 bytes
  let (trackingNumber, bytes) ← decodeUInt 2 bytes
  let (orderReferenceNumber, bytes) ← decodeUInt 8 bytes
  pure ({ timestamp, trackingNumber, orderReferenceNumber }, bytes)

@[simp] theorem encode_length (message : OrderDeleteMessage) : (encode message).length = 18 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length]

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
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end OrderDeleteMessage

/-- Order Book Flush Message: 14 bytes -/
structure OrderBookFlushMessage where
  timestamp : BitVec 64
  trackingNumber : BitVec 16
  orderBook : BitVec 32
  deriving DecidableEq, Repr

namespace OrderBookFlushMessage

def encode (message : OrderBookFlushMessage) : List UInt8 :=
  encodeUInt 8 message.timestamp
    ++ (encodeUInt 2 message.trackingNumber
    ++ (encodeUInt 4 message.orderBook))

def decode (bytes : List UInt8) : Option (OrderBookFlushMessage × List UInt8) := do
  let (timestamp, bytes) ← decodeUInt 8 bytes
  let (trackingNumber, bytes) ← decodeUInt 2 bytes
  let (orderBook, bytes) ← decodeUInt 4 bytes
  pure ({ timestamp, trackingNumber, orderBook }, bytes)

@[simp] theorem encode_length (message : OrderBookFlushMessage) : (encode message).length = 14 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length]

theorem encode_length_pos (message : OrderBookFlushMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OrderBookFlushMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end OrderBookFlushMessage

/-- Order Replace Message: 34 bytes -/
structure OrderReplaceMessage where
  timestamp : BitVec 64
  trackingNumber : BitVec 16
  originalOrderReferenceNumber : BitVec 64
  newOrderReferenceNumber : BitVec 64
  quantity : BitVec 32
  price : BitVec 32
  deriving DecidableEq, Repr

namespace OrderReplaceMessage

def encode (message : OrderReplaceMessage) : List UInt8 :=
  encodeUInt 8 message.timestamp
    ++ (encodeUInt 2 message.trackingNumber
    ++ (encodeUInt 8 message.originalOrderReferenceNumber
    ++ (encodeUInt 8 message.newOrderReferenceNumber
    ++ (encodeUInt 4 message.quantity
    ++ (encodeUInt 4 message.price)))))

def decode (bytes : List UInt8) : Option (OrderReplaceMessage × List UInt8) := do
  let (timestamp, bytes) ← decodeUInt 8 bytes
  let (trackingNumber, bytes) ← decodeUInt 2 bytes
  let (originalOrderReferenceNumber, bytes) ← decodeUInt 8 bytes
  let (newOrderReferenceNumber, bytes) ← decodeUInt 8 bytes
  let (quantity, bytes) ← decodeUInt 4 bytes
  let (price, bytes) ← decodeUInt 4 bytes
  pure ({ timestamp, trackingNumber, originalOrderReferenceNumber, newOrderReferenceNumber, quantity, price }, bytes)

@[simp] theorem encode_length (message : OrderReplaceMessage) : (encode message).length = 34 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length]

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
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end OrderReplaceMessage

/-- Trade Message: 43 bytes -/
structure TradeMessage where
  timestamp : BitVec 64
  trackingNumber : BitVec 16
  orderReferenceNumber : BitVec 64
  tradeType : TradeType
  quantity : BitVec 32
  orderBook : BitVec 32
  matchNumber : BitVec 32
  tradePrice : BitVec 32
  participantIdBuyer : Alpha 4
  participantIdSeller : Alpha 4
  deriving DecidableEq, Repr

namespace TradeMessage

def encode (message : TradeMessage) : List UInt8 :=
  encodeUInt 8 message.timestamp
    ++ (encodeUInt 2 message.trackingNumber
    ++ (encodeUInt 8 message.orderReferenceNumber
    ++ (TradeType.encode message.tradeType
    ++ (encodeUInt 4 message.quantity
    ++ (encodeUInt 4 message.orderBook
    ++ (encodeUInt 4 message.matchNumber
    ++ (encodeUInt 4 message.tradePrice
    ++ (Alpha.encode message.participantIdBuyer
    ++ (Alpha.encode message.participantIdSeller)))))))))

def decode (bytes : List UInt8) : Option (TradeMessage × List UInt8) := do
  let (timestamp, bytes) ← decodeUInt 8 bytes
  let (trackingNumber, bytes) ← decodeUInt 2 bytes
  let (orderReferenceNumber, bytes) ← decodeUInt 8 bytes
  let (tradeType, bytes) ← TradeType.decode bytes
  let (quantity, bytes) ← decodeUInt 4 bytes
  let (orderBook, bytes) ← decodeUInt 4 bytes
  let (matchNumber, bytes) ← decodeUInt 4 bytes
  let (tradePrice, bytes) ← decodeUInt 4 bytes
  let (participantIdBuyer, bytes) ← Alpha.decode 4 bytes
  let (participantIdSeller, bytes) ← Alpha.decode 4 bytes
  pure ({ timestamp, trackingNumber, orderReferenceNumber, tradeType, quantity, orderBook, matchNumber, tradePrice, participantIdBuyer, participantIdSeller }, bytes)

@[simp] theorem encode_length (message : TradeMessage) : (encode message).length = 43 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, TradeType.encode_length, Alpha.encode_length]

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
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, TradeType.decode_encode, some_bind]
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
  rw [Alpha.decode_encode, some_bind]
  rfl

end TradeMessage

/-- Cross Trade Message: 31 bytes -/
structure CrossTradeMessage where
  timestamp : BitVec 64
  trackingNumber : BitVec 16
  quantity : BitVec 32
  orderBook : BitVec 32
  crossPrice : BitVec 32
  matchNumber : BitVec 32
  crossType : CrossType
  numberOfTrades : BitVec 32
  deriving DecidableEq, Repr

namespace CrossTradeMessage

def encode (message : CrossTradeMessage) : List UInt8 :=
  encodeUInt 8 message.timestamp
    ++ (encodeUInt 2 message.trackingNumber
    ++ (encodeUInt 4 message.quantity
    ++ (encodeUInt 4 message.orderBook
    ++ (encodeUInt 4 message.crossPrice
    ++ (encodeUInt 4 message.matchNumber
    ++ (CrossType.encode message.crossType
    ++ (encodeUInt 4 message.numberOfTrades)))))))

def decode (bytes : List UInt8) : Option (CrossTradeMessage × List UInt8) := do
  let (timestamp, bytes) ← decodeUInt 8 bytes
  let (trackingNumber, bytes) ← decodeUInt 2 bytes
  let (quantity, bytes) ← decodeUInt 4 bytes
  let (orderBook, bytes) ← decodeUInt 4 bytes
  let (crossPrice, bytes) ← decodeUInt 4 bytes
  let (matchNumber, bytes) ← decodeUInt 4 bytes
  let (crossType, bytes) ← CrossType.decode bytes
  let (numberOfTrades, bytes) ← decodeUInt 4 bytes
  pure ({ timestamp, trackingNumber, quantity, orderBook, crossPrice, matchNumber, crossType, numberOfTrades }, bytes)

@[simp] theorem encode_length (message : CrossTradeMessage) : (encode message).length = 31 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, CrossType.encode_length]

theorem encode_length_pos (message : CrossTradeMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : CrossTradeMessage) (rest : List UInt8) :
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
  rw [List.append_assoc, CrossType.decode_encode, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end CrossTradeMessage

/-- Broken Trade Message: 14 bytes -/
structure BrokenTradeMessage where
  timestamp : BitVec 64
  trackingNumber : BitVec 16
  matchNumber : BitVec 32
  deriving DecidableEq, Repr

namespace BrokenTradeMessage

def encode (message : BrokenTradeMessage) : List UInt8 :=
  encodeUInt 8 message.timestamp
    ++ (encodeUInt 2 message.trackingNumber
    ++ (encodeUInt 4 message.matchNumber))

def decode (bytes : List UInt8) : Option (BrokenTradeMessage × List UInt8) := do
  let (timestamp, bytes) ← decodeUInt 8 bytes
  let (trackingNumber, bytes) ← decodeUInt 2 bytes
  let (matchNumber, bytes) ← decodeUInt 4 bytes
  pure ({ timestamp, trackingNumber, matchNumber }, bytes)

@[simp] theorem encode_length (message : BrokenTradeMessage) : (encode message).length = 14 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length]

theorem encode_length_pos (message : BrokenTradeMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : BrokenTradeMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end BrokenTradeMessage

/-- Noii Message: 60 bytes -/
structure NoiiMessage where
  timestamp : BitVec 64
  trackingNumber : BitVec 16
  pairedQuantity : BitVec 64
  imbalanceQuantity : BitVec 64
  imbalanceDirection : ImbalanceDirection
  orderBook : BitVec 32
  equilibriumPrice : BitVec 32
  crossType : CrossType
  bestBidPrice : BitVec 32
  bestBidQuantity : BitVec 64
  bestAskPrice : BitVec 32
  bestAskQuantity : BitVec 64
  deriving DecidableEq, Repr

namespace NoiiMessage

def encode (message : NoiiMessage) : List UInt8 :=
  encodeUInt 8 message.timestamp
    ++ (encodeUInt 2 message.trackingNumber
    ++ (encodeUInt 8 message.pairedQuantity
    ++ (encodeUInt 8 message.imbalanceQuantity
    ++ (ImbalanceDirection.encode message.imbalanceDirection
    ++ (encodeUInt 4 message.orderBook
    ++ (encodeUInt 4 message.equilibriumPrice
    ++ (CrossType.encode message.crossType
    ++ (encodeUInt 4 message.bestBidPrice
    ++ (encodeUInt 8 message.bestBidQuantity
    ++ (encodeUInt 4 message.bestAskPrice
    ++ (encodeUInt 8 message.bestAskQuantity)))))))))))

def decode (bytes : List UInt8) : Option (NoiiMessage × List UInt8) := do
  let (timestamp, bytes) ← decodeUInt 8 bytes
  let (trackingNumber, bytes) ← decodeUInt 2 bytes
  let (pairedQuantity, bytes) ← decodeUInt 8 bytes
  let (imbalanceQuantity, bytes) ← decodeUInt 8 bytes
  let (imbalanceDirection, bytes) ← ImbalanceDirection.decode bytes
  let (orderBook, bytes) ← decodeUInt 4 bytes
  let (equilibriumPrice, bytes) ← decodeUInt 4 bytes
  let (crossType, bytes) ← CrossType.decode bytes
  let (bestBidPrice, bytes) ← decodeUInt 4 bytes
  let (bestBidQuantity, bytes) ← decodeUInt 8 bytes
  let (bestAskPrice, bytes) ← decodeUInt 4 bytes
  let (bestAskQuantity, bytes) ← decodeUInt 8 bytes
  pure ({ timestamp, trackingNumber, pairedQuantity, imbalanceQuantity, imbalanceDirection, orderBook, equilibriumPrice, crossType, bestBidPrice, bestBidQuantity, bestAskPrice, bestAskQuantity }, bytes)

@[simp] theorem encode_length (message : NoiiMessage) : (encode message).length = 60 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, ImbalanceDirection.encode_length, CrossType.encode_length]

theorem encode_length_pos (message : NoiiMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : NoiiMessage) (rest : List UInt8) :
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
  rw [List.append_assoc, ImbalanceDirection.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, CrossType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end NoiiMessage

/-- Moii Message: 28 bytes -/
structure MoiiMessage where
  timestamp : BitVec 64
  trackingNumber : BitVec 16
  pairedQuantity : BitVec 64
  orderBook : BitVec 32
  equilibriumPrice : BitVec 32
  crossType : CrossType
  crossLevel : CrossLevel
  deriving DecidableEq, Repr

namespace MoiiMessage

def encode (message : MoiiMessage) : List UInt8 :=
  encodeUInt 8 message.timestamp
    ++ (encodeUInt 2 message.trackingNumber
    ++ (encodeUInt 8 message.pairedQuantity
    ++ (encodeUInt 4 message.orderBook
    ++ (encodeUInt 4 message.equilibriumPrice
    ++ (CrossType.encode message.crossType
    ++ (CrossLevel.encode message.crossLevel))))))

def decode (bytes : List UInt8) : Option (MoiiMessage × List UInt8) := do
  let (timestamp, bytes) ← decodeUInt 8 bytes
  let (trackingNumber, bytes) ← decodeUInt 2 bytes
  let (pairedQuantity, bytes) ← decodeUInt 8 bytes
  let (orderBook, bytes) ← decodeUInt 4 bytes
  let (equilibriumPrice, bytes) ← decodeUInt 4 bytes
  let (crossType, bytes) ← CrossType.decode bytes
  let (crossLevel, bytes) ← CrossLevel.decode bytes
  pure ({ timestamp, trackingNumber, pairedQuantity, orderBook, equilibriumPrice, crossType, crossLevel }, bytes)

@[simp] theorem encode_length (message : MoiiMessage) : (encode message).length = 28 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, CrossType.encode_length, CrossLevel.encode_length]

theorem encode_length_pos (message : MoiiMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : MoiiMessage) (rest : List UInt8) :
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
  rw [List.append_assoc, CrossType.decode_encode, some_bind]
  dsimp only
  rw [CrossLevel.decode_encode, some_bind]
  rfl

end MoiiMessage

/-- Execution Summary Message: 37 bytes -/
structure ExecutionSummaryMessage where
  timestamp : BitVec 64
  trackingNumber : BitVec 16
  orderBook : BitVec 32
  aggressingSide : AggressingSide
  quantity : BitVec 32
  hiddenQuantity : BitVec 32
  stpCancelQuantity : BitVec 32
  farPrice : BitVec 32
  addQuantity : BitVec 32
  numberOfLitExecutions : BitVec 16
  deriving DecidableEq, Repr

namespace ExecutionSummaryMessage

def encode (message : ExecutionSummaryMessage) : List UInt8 :=
  encodeUInt 8 message.timestamp
    ++ (encodeUInt 2 message.trackingNumber
    ++ (encodeUInt 4 message.orderBook
    ++ (AggressingSide.encode message.aggressingSide
    ++ (encodeUInt 4 message.quantity
    ++ (encodeUInt 4 message.hiddenQuantity
    ++ (encodeUInt 4 message.stpCancelQuantity
    ++ (encodeUInt 4 message.farPrice
    ++ (encodeUInt 4 message.addQuantity
    ++ (encodeUInt 2 message.numberOfLitExecutions)))))))))

def decode (bytes : List UInt8) : Option (ExecutionSummaryMessage × List UInt8) := do
  let (timestamp, bytes) ← decodeUInt 8 bytes
  let (trackingNumber, bytes) ← decodeUInt 2 bytes
  let (orderBook, bytes) ← decodeUInt 4 bytes
  let (aggressingSide, bytes) ← AggressingSide.decode bytes
  let (quantity, bytes) ← decodeUInt 4 bytes
  let (hiddenQuantity, bytes) ← decodeUInt 4 bytes
  let (stpCancelQuantity, bytes) ← decodeUInt 4 bytes
  let (farPrice, bytes) ← decodeUInt 4 bytes
  let (addQuantity, bytes) ← decodeUInt 4 bytes
  let (numberOfLitExecutions, bytes) ← decodeUInt 2 bytes
  pure ({ timestamp, trackingNumber, orderBook, aggressingSide, quantity, hiddenQuantity, stpCancelQuantity, farPrice, addQuantity, numberOfLitExecutions }, bytes)

@[simp] theorem encode_length (message : ExecutionSummaryMessage) : (encode message).length = 37 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, AggressingSide.encode_length]

theorem encode_length_pos (message : ExecutionSummaryMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : ExecutionSummaryMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, AggressingSide.decode_encode, some_bind]
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

end ExecutionSummaryMessage

/-- Any Payload, selected by Message Type -/
inductive Payload where
  | systemEventMessage (message : SystemEventMessage) -- "S" 0x53
  | orderBookTradingActionMessage (message : OrderBookTradingActionMessage) -- "H" 0x48
  | orderBookDirectoryMessage (message : OrderBookDirectoryMessage) -- "R" 0x52
  | addOrderMessage (message : AddOrderMessage) -- "A" 0x41
  | addOrderMpidAttributionMessage (message : AddOrderMpidAttributionMessage) -- "F" 0x46
  | orderExecutedMessage (message : OrderExecutedMessage) -- "E" 0x45
  | orderExecutedWithPriceMessage (message : OrderExecutedWithPriceMessage) -- "C" 0x43
  | orderCancelMessage (message : OrderCancelMessage) -- "X" 0x58
  | orderDeleteMessage (message : OrderDeleteMessage) -- "D" 0x44
  | orderBookFlushMessage (message : OrderBookFlushMessage) -- "Y" 0x59
  | orderReplaceMessage (message : OrderReplaceMessage) -- "U" 0x55
  | tradeMessage (message : TradeMessage) -- "P" 0x50
  | crossTradeMessage (message : CrossTradeMessage) -- "Q" 0x51
  | brokenTradeMessage (message : BrokenTradeMessage) -- "B" 0x42
  | noiiMessage (message : NoiiMessage) -- "I" 0x49
  | moiiMessage (message : MoiiMessage) -- "J" 0x4A
  | executionSummaryMessage (message : ExecutionSummaryMessage) -- "K" 0x4B
  deriving DecidableEq, Repr

namespace Payload

/-- The Message Type each message is sent under -/
def tag : Payload → BitVec 8
  | .systemEventMessage _ => 83
  | .orderBookTradingActionMessage _ => 72
  | .orderBookDirectoryMessage _ => 82
  | .addOrderMessage _ => 65
  | .addOrderMpidAttributionMessage _ => 70
  | .orderExecutedMessage _ => 69
  | .orderExecutedWithPriceMessage _ => 67
  | .orderCancelMessage _ => 88
  | .orderDeleteMessage _ => 68
  | .orderBookFlushMessage _ => 89
  | .orderReplaceMessage _ => 85
  | .tradeMessage _ => 80
  | .crossTradeMessage _ => 81
  | .brokenTradeMessage _ => 66
  | .noiiMessage _ => 73
  | .moiiMessage _ => 74
  | .executionSummaryMessage _ => 75

def encode : Payload → List UInt8
  | .systemEventMessage message => SystemEventMessage.encode message
  | .orderBookTradingActionMessage message => OrderBookTradingActionMessage.encode message
  | .orderBookDirectoryMessage message => OrderBookDirectoryMessage.encode message
  | .addOrderMessage message => AddOrderMessage.encode message
  | .addOrderMpidAttributionMessage message => AddOrderMpidAttributionMessage.encode message
  | .orderExecutedMessage message => OrderExecutedMessage.encode message
  | .orderExecutedWithPriceMessage message => OrderExecutedWithPriceMessage.encode message
  | .orderCancelMessage message => OrderCancelMessage.encode message
  | .orderDeleteMessage message => OrderDeleteMessage.encode message
  | .orderBookFlushMessage message => OrderBookFlushMessage.encode message
  | .orderReplaceMessage message => OrderReplaceMessage.encode message
  | .tradeMessage message => TradeMessage.encode message
  | .crossTradeMessage message => CrossTradeMessage.encode message
  | .brokenTradeMessage message => BrokenTradeMessage.encode message
  | .noiiMessage message => NoiiMessage.encode message
  | .moiiMessage message => MoiiMessage.encode message
  | .executionSummaryMessage message => ExecutionSummaryMessage.encode message

/-- The most bytes any message's encoding can take -/
theorem encode_length_le (message : Payload) : (encode message).length ≤ 100 := by
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
  | orderExecutedMessage inner =>
    simp only [encode, OrderExecutedMessage.encode_length]
    omega
  | orderExecutedWithPriceMessage inner =>
    simp only [encode, OrderExecutedWithPriceMessage.encode_length]
    omega
  | orderCancelMessage inner =>
    simp only [encode, OrderCancelMessage.encode_length]
    omega
  | orderDeleteMessage inner =>
    simp only [encode, OrderDeleteMessage.encode_length]
    omega
  | orderBookFlushMessage inner =>
    simp only [encode, OrderBookFlushMessage.encode_length]
    omega
  | orderReplaceMessage inner =>
    simp only [encode, OrderReplaceMessage.encode_length]
    omega
  | tradeMessage inner =>
    simp only [encode, TradeMessage.encode_length]
    omega
  | crossTradeMessage inner =>
    simp only [encode, CrossTradeMessage.encode_length]
    omega
  | brokenTradeMessage inner =>
    simp only [encode, BrokenTradeMessage.encode_length]
    omega
  | noiiMessage inner =>
    simp only [encode, NoiiMessage.encode_length]
    omega
  | moiiMessage inner =>
    simp only [encode, MoiiMessage.encode_length]
    omega
  | executionSummaryMessage inner =>
    simp only [encode, ExecutionSummaryMessage.encode_length]
    omega

def decode (tag : BitVec 8) (bytes : List UInt8) : Option (Payload × List UInt8) :=
  if tag = 83 then (SystemEventMessage.decode bytes).map fun (message, rest) => (.systemEventMessage message, rest)
  else if tag = 72 then (OrderBookTradingActionMessage.decode bytes).map fun (message, rest) => (.orderBookTradingActionMessage message, rest)
  else if tag = 82 then (OrderBookDirectoryMessage.decode bytes).map fun (message, rest) => (.orderBookDirectoryMessage message, rest)
  else if tag = 65 then (AddOrderMessage.decode bytes).map fun (message, rest) => (.addOrderMessage message, rest)
  else if tag = 70 then (AddOrderMpidAttributionMessage.decode bytes).map fun (message, rest) => (.addOrderMpidAttributionMessage message, rest)
  else if tag = 69 then (OrderExecutedMessage.decode bytes).map fun (message, rest) => (.orderExecutedMessage message, rest)
  else if tag = 67 then (OrderExecutedWithPriceMessage.decode bytes).map fun (message, rest) => (.orderExecutedWithPriceMessage message, rest)
  else if tag = 88 then (OrderCancelMessage.decode bytes).map fun (message, rest) => (.orderCancelMessage message, rest)
  else if tag = 68 then (OrderDeleteMessage.decode bytes).map fun (message, rest) => (.orderDeleteMessage message, rest)
  else if tag = 89 then (OrderBookFlushMessage.decode bytes).map fun (message, rest) => (.orderBookFlushMessage message, rest)
  else if tag = 85 then (OrderReplaceMessage.decode bytes).map fun (message, rest) => (.orderReplaceMessage message, rest)
  else if tag = 80 then (TradeMessage.decode bytes).map fun (message, rest) => (.tradeMessage message, rest)
  else if tag = 81 then (CrossTradeMessage.decode bytes).map fun (message, rest) => (.crossTradeMessage message, rest)
  else if tag = 66 then (BrokenTradeMessage.decode bytes).map fun (message, rest) => (.brokenTradeMessage message, rest)
  else if tag = 73 then (NoiiMessage.decode bytes).map fun (message, rest) => (.noiiMessage message, rest)
  else if tag = 74 then (MoiiMessage.decode bytes).map fun (message, rest) => (.moiiMessage message, rest)
  else if tag = 75 then (ExecutionSummaryMessage.decode bytes).map fun (message, rest) => (.executionSummaryMessage message, rest)
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
  | systemEventMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, SystemEventMessage.encode_length]
    omega
  | orderBookTradingActionMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, OrderBookTradingActionMessage.encode_length]
    omega
  | orderBookDirectoryMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, OrderBookDirectoryMessage.encode_length]
    omega
  | addOrderMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, AddOrderMessage.encode_length]
    omega
  | addOrderMpidAttributionMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, AddOrderMpidAttributionMessage.encode_length]
    omega
  | orderExecutedMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, OrderExecutedMessage.encode_length]
    omega
  | orderExecutedWithPriceMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, OrderExecutedWithPriceMessage.encode_length]
    omega
  | orderCancelMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, OrderCancelMessage.encode_length]
    omega
  | orderDeleteMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, OrderDeleteMessage.encode_length]
    omega
  | orderBookFlushMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, OrderBookFlushMessage.encode_length]
    omega
  | orderReplaceMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, OrderReplaceMessage.encode_length]
    omega
  | tradeMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, TradeMessage.encode_length]
    omega
  | crossTradeMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, CrossTradeMessage.encode_length]
    omega
  | brokenTradeMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, BrokenTradeMessage.encode_length]
    omega
  | noiiMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, NoiiMessage.encode_length]
    omega
  | moiiMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, MoiiMessage.encode_length]
    omega
  | executionSummaryMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, ExecutionSummaryMessage.encode_length]
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

end Omi.NasdaqNordicequitiesTotalviewItchV304X
