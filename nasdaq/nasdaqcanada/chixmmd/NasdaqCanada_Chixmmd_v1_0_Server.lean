import Omi.Wire

/-!
# National Association of Securities Dealers Automated Quotations (Nasdaq) CHIXMMD Multicast Market Data v1.0

Generated from the binary model, with the proofs the model's rules call for: every record
decodes back to what was encoded; a message dispatch selects the message its type names;
a count is written from the list it counts; a length prefix is written from the bytes it frames;
and a packet read to the end of its data decodes to the messages that were written.

Text fields are kept byte for byte, padding included, so what is decoded encodes back unchanged.
Prices with implied decimals are proven as the integers on the wire.
-/

namespace Omi.NasdaqNasdaqcanadaChixmmdGlimpseV10Server

/-- Event Code: one byte code -/
def EventCode.codes : List UInt8 :=
  [0x4F, 0x53, 0x51, 0x4D, 0x45, 0x43, 0x57, 0x52]

inductive EventCode where
  | startOfMessages -- Start Of Messages
  | startOfNasdaqCanadaTradingSession -- Start Of Nasdaq Canada Trading Session
  | startOfPrimaryMarketTradingSession -- Start Of Primary Market Trading Session
  | endOfPrimaryMarketTradingSession -- End Of Primary Market Trading Session
  | endOfSystemHours -- End Of System Hours
  | endOfMessages -- End Of Messages
  | marketWideCircuitBreakerHalt -- Market Wide Circuit Breaker Halt
  | marketWideCircuitBreakerResumption -- Market Wide Circuit Breaker Resumption
  | unlisted (byte : { byte : UInt8 // byte ∉ EventCode.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace EventCode

def toByte : EventCode → UInt8
  | .startOfMessages => 0x4F
  | .startOfNasdaqCanadaTradingSession => 0x53
  | .startOfPrimaryMarketTradingSession => 0x51
  | .endOfPrimaryMarketTradingSession => 0x4D
  | .endOfSystemHours => 0x45
  | .endOfMessages => 0x43
  | .marketWideCircuitBreakerHalt => 0x57
  | .marketWideCircuitBreakerResumption => 0x52
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : EventCode :=
  if byte = 0x4F then .startOfMessages
  else if byte = 0x53 then .startOfNasdaqCanadaTradingSession
  else if byte = 0x51 then .startOfPrimaryMarketTradingSession
  else if byte = 0x4D then .endOfPrimaryMarketTradingSession
  else if byte = 0x45 then .endOfSystemHours
  else if byte = 0x43 then .endOfMessages
  else if byte = 0x57 then .marketWideCircuitBreakerHalt
  else .marketWideCircuitBreakerResumption

def ofByte (byte : UInt8) : EventCode :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : EventCode) : ofByte value.toByte = value := by
  cases value with
  | startOfMessages => decide
  | startOfNasdaqCanadaTradingSession => decide
  | startOfPrimaryMarketTradingSession => decide
  | endOfPrimaryMarketTradingSession => decide
  | endOfSystemHours => decide
  | endOfMessages => decide
  | marketWideCircuitBreakerHalt => decide
  | marketWideCircuitBreakerResumption => decide
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

/-- Trading State: one byte code -/
def TradingState.codes : List UInt8 :=
  [0x48, 0x54]

inductive TradingState where
  | halted -- Halted
  | trading -- Trading
  | unlisted (byte : { byte : UInt8 // byte ∉ TradingState.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace TradingState

def toByte : TradingState → UInt8
  | .halted => 0x48
  | .trading => 0x54
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : TradingState :=
  if byte = 0x48 then .halted
  else .trading

def ofByte (byte : UInt8) : TradingState :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : TradingState) : ofByte value.toByte = value := by
  cases value with
  | halted => decide
  | trading => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : TradingState) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (TradingState × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : TradingState) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : TradingState) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end TradingState

/-- Listing Market: one byte code -/
def ListingMarket.codes : List UInt8 :=
  [0x54, 0x56, 0x43, 0x4E]

inductive ListingMarket where
  | tsx -- Tsx
  | tsxVenture -- Tsx Venture
  | cse -- Cse
  | neo -- Neo
  | unlisted (byte : { byte : UInt8 // byte ∉ ListingMarket.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace ListingMarket

def toByte : ListingMarket → UInt8
  | .tsx => 0x54
  | .tsxVenture => 0x56
  | .cse => 0x43
  | .neo => 0x4E
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : ListingMarket :=
  if byte = 0x54 then .tsx
  else if byte = 0x56 then .tsxVenture
  else if byte = 0x43 then .cse
  else .neo

def ofByte (byte : UInt8) : ListingMarket :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : ListingMarket) : ofByte value.toByte = value := by
  cases value with
  | tsx => decide
  | tsxVenture => decide
  | cse => decide
  | neo => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : ListingMarket) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (ListingMarket × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : ListingMarket) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : ListingMarket) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end ListingMarket

/-- Gef Eligible: one byte code -/
def GefEligible.codes : List UInt8 :=
  [0x59, 0x4E]

inductive GefEligible where
  | gefEligible -- Gef Eligible
  | notGefEligible -- Not Gef Eligible
  | unlisted (byte : { byte : UInt8 // byte ∉ GefEligible.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace GefEligible

def toByte : GefEligible → UInt8
  | .gefEligible => 0x59
  | .notGefEligible => 0x4E
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : GefEligible :=
  if byte = 0x59 then .gefEligible
  else .notGefEligible

def ofByte (byte : UInt8) : GefEligible :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : GefEligible) : ofByte value.toByte = value := by
  cases value with
  | gefEligible => decide
  | notGefEligible => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : GefEligible) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (GefEligible × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : GefEligible) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : GefEligible) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end GefEligible

/-- Buy Sell Indicator: one byte code -/
def BuySellIndicator.codes : List UInt8 :=
  [0x42, 0x53]

inductive BuySellIndicator where
  | buy -- Buy
  | sell -- Sell
  | unlisted (byte : { byte : UInt8 // byte ∉ BuySellIndicator.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace BuySellIndicator

def toByte : BuySellIndicator → UInt8
  | .buy => 0x42
  | .sell => 0x53
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : BuySellIndicator :=
  if byte = 0x42 then .buy
  else .sell

def ofByte (byte : UInt8) : BuySellIndicator :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : BuySellIndicator) : ofByte value.toByte = value := by
  cases value with
  | buy => decide
  | sell => decide
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

/-- Login Accepted Packet: 20 bytes -/
structure LoginAcceptedPacket where
  session : Alpha 10
  sequenceNumber : Alpha 10
  deriving DecidableEq, Repr

namespace LoginAcceptedPacket

def encode (message : LoginAcceptedPacket) : List UInt8 :=
  Alpha.encode message.session
    ++ (Alpha.encode message.sequenceNumber)

def decode (bytes : List UInt8) : Option (LoginAcceptedPacket × List UInt8) := do
  let (session, bytes) ← Alpha.decode 10 bytes
  let (sequenceNumber, bytes) ← Alpha.decode 10 bytes
  pure ({ session, sequenceNumber }, bytes)

@[simp] theorem encode_length (message : LoginAcceptedPacket) : (encode message).length = 20 := by
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

/-- System Event Message: 1 bytes -/
structure SystemEventMessage where
  eventCode : EventCode
  deriving DecidableEq, Repr

namespace SystemEventMessage

def encode (message : SystemEventMessage) : List UInt8 :=
  EventCode.encode message.eventCode

def decode (bytes : List UInt8) : Option (SystemEventMessage × List UInt8) := do
  let (eventCode, bytes) ← EventCode.decode bytes
  pure ({ eventCode }, bytes)

@[simp] theorem encode_length (message : SystemEventMessage) : (encode message).length = 1 := by
  unfold encode
  simp only [EventCode.encode_length]

theorem encode_length_pos (message : SystemEventMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SystemEventMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [EventCode.decode_encode, some_bind]
  rfl

end SystemEventMessage

/-- Stock Status Message: 21 bytes -/
structure StockStatusMessage where
  stock : Alpha 10
  tradingState : TradingState
  reserved1 : Alpha 1
  listingMarket : ListingMarket
  boardLotSize : Alpha 4
  currency : Alpha 3
  gefEligible : GefEligible
  deriving DecidableEq, Repr

namespace StockStatusMessage

def encode (message : StockStatusMessage) : List UInt8 :=
  Alpha.encode message.stock
    ++ (TradingState.encode message.tradingState
    ++ (Alpha.encode message.reserved1
    ++ (ListingMarket.encode message.listingMarket
    ++ (Alpha.encode message.boardLotSize
    ++ (Alpha.encode message.currency
    ++ (GefEligible.encode message.gefEligible))))))

def decode (bytes : List UInt8) : Option (StockStatusMessage × List UInt8) := do
  let (stock, bytes) ← Alpha.decode 10 bytes
  let (tradingState, bytes) ← TradingState.decode bytes
  let (reserved1, bytes) ← Alpha.decode 1 bytes
  let (listingMarket, bytes) ← ListingMarket.decode bytes
  let (boardLotSize, bytes) ← Alpha.decode 4 bytes
  let (currency, bytes) ← Alpha.decode 3 bytes
  let (gefEligible_, bytes) ← GefEligible.decode bytes
  pure ({ stock, tradingState, reserved1, listingMarket, boardLotSize, currency, gefEligible := gefEligible_ }, bytes)

@[simp] theorem encode_length (message : StockStatusMessage) : (encode message).length = 21 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, TradingState.encode_length, ListingMarket.encode_length, GefEligible.encode_length]

theorem encode_length_pos (message : StockStatusMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : StockStatusMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, TradingState.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, ListingMarket.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [GefEligible.decode_encode, some_bind]
  rfl

end StockStatusMessage

/-- Add Order Message: 39 bytes -/
structure AddOrderMessage where
  orderReference : Alpha 9
  buySellIndicator : BuySellIndicator
  shares : Alpha 6
  stock : Alpha 10
  price : Alpha 10
  broker : Alpha 3
  deriving DecidableEq, Repr

namespace AddOrderMessage

def encode (message : AddOrderMessage) : List UInt8 :=
  Alpha.encode message.orderReference
    ++ (BuySellIndicator.encode message.buySellIndicator
    ++ (Alpha.encode message.shares
    ++ (Alpha.encode message.stock
    ++ (Alpha.encode message.price
    ++ (Alpha.encode message.broker)))))

def decode (bytes : List UInt8) : Option (AddOrderMessage × List UInt8) := do
  let (orderReference, bytes) ← Alpha.decode 9 bytes
  let (buySellIndicator, bytes) ← BuySellIndicator.decode bytes
  let (shares, bytes) ← Alpha.decode 6 bytes
  let (stock, bytes) ← Alpha.decode 10 bytes
  let (price, bytes) ← Alpha.decode 10 bytes
  let (broker, bytes) ← Alpha.decode 3 bytes
  pure ({ orderReference, buySellIndicator, shares, stock, price, broker }, bytes)

@[simp] theorem encode_length (message : AddOrderMessage) : (encode message).length = 39 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, BuySellIndicator.encode_length]

theorem encode_length_pos (message : AddOrderMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : AddOrderMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, BuySellIndicator.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end AddOrderMessage

/-- Long Form Add Order Message: 52 bytes -/
structure LongFormAddOrderMessage where
  orderReference : Alpha 9
  buySellIndicator : BuySellIndicator
  longShares : Alpha 10
  stock : Alpha 10
  longPrice : Alpha 19
  broker : Alpha 3
  deriving DecidableEq, Repr

namespace LongFormAddOrderMessage

def encode (message : LongFormAddOrderMessage) : List UInt8 :=
  Alpha.encode message.orderReference
    ++ (BuySellIndicator.encode message.buySellIndicator
    ++ (Alpha.encode message.longShares
    ++ (Alpha.encode message.stock
    ++ (Alpha.encode message.longPrice
    ++ (Alpha.encode message.broker)))))

def decode (bytes : List UInt8) : Option (LongFormAddOrderMessage × List UInt8) := do
  let (orderReference, bytes) ← Alpha.decode 9 bytes
  let (buySellIndicator, bytes) ← BuySellIndicator.decode bytes
  let (longShares, bytes) ← Alpha.decode 10 bytes
  let (stock, bytes) ← Alpha.decode 10 bytes
  let (longPrice, bytes) ← Alpha.decode 19 bytes
  let (broker, bytes) ← Alpha.decode 3 bytes
  pure ({ orderReference, buySellIndicator, longShares, stock, longPrice, broker }, bytes)

@[simp] theorem encode_length (message : LongFormAddOrderMessage) : (encode message).length = 52 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, BuySellIndicator.encode_length]

theorem encode_length_pos (message : LongFormAddOrderMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : LongFormAddOrderMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, BuySellIndicator.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end LongFormAddOrderMessage

/-- Any Sequenced Message, selected by Message Type -/
inductive SequencedMessage where
  | systemEventMessage (message : SystemEventMessage) -- "S" 0x53
  | stockStatusMessage (message : StockStatusMessage) -- "H" 0x48
  | addOrderMessage (message : AddOrderMessage) -- "A" 0x41
  | longFormAddOrderMessage (message : LongFormAddOrderMessage) -- "a" 0x61
  deriving DecidableEq, Repr

namespace SequencedMessage

/-- The Message Type each message is sent under -/
def tag : SequencedMessage → BitVec 8
  | .systemEventMessage _ => 83
  | .stockStatusMessage _ => 72
  | .addOrderMessage _ => 65
  | .longFormAddOrderMessage _ => 97

def encode : SequencedMessage → List UInt8
  | .systemEventMessage message => SystemEventMessage.encode message
  | .stockStatusMessage message => StockStatusMessage.encode message
  | .addOrderMessage message => AddOrderMessage.encode message
  | .longFormAddOrderMessage message => LongFormAddOrderMessage.encode message

/-- The most bytes any message's encoding can take -/
theorem encode_length_le (message : SequencedMessage) : (encode message).length ≤ 52 := by
  cases message with
  | systemEventMessage inner =>
    simp only [encode, SystemEventMessage.encode_length]
    omega
  | stockStatusMessage inner =>
    simp only [encode, StockStatusMessage.encode_length]
    omega
  | addOrderMessage inner =>
    simp only [encode, AddOrderMessage.encode_length]
    omega
  | longFormAddOrderMessage inner =>
    simp only [encode, LongFormAddOrderMessage.encode_length]
    omega

def decode (tag : BitVec 8) (bytes : List UInt8) : Option (SequencedMessage × List UInt8) :=
  if tag = 83 then (SystemEventMessage.decode bytes).map fun (message, rest) => (.systemEventMessage message, rest)
  else if tag = 72 then (StockStatusMessage.decode bytes).map fun (message, rest) => (.stockStatusMessage message, rest)
  else if tag = 65 then (AddOrderMessage.decode bytes).map fun (message, rest) => (.addOrderMessage message, rest)
  else if tag = 97 then (LongFormAddOrderMessage.decode bytes).map fun (message, rest) => (.longFormAddOrderMessage message, rest)
  else none

@[simp] theorem decode_encode (message : SequencedMessage) (rest : List UInt8) :
    decode (tag message) (encode message ++ rest) = some (message, rest) := by
  cases message <;> simp [decode, encode, tag]

end SequencedMessage

/-- Sequenced Data Packet -/
structure SequencedDataPacket where
  timestamp : Alpha 8
  sequencedMessage : SequencedMessage
  deriving DecidableEq, Repr

namespace SequencedDataPacket

def encode (message : SequencedDataPacket) : List UInt8 :=
  Alpha.encode message.timestamp
    ++ (encodeUInt 1 (SequencedMessage.tag message.sequencedMessage)
    ++ (SequencedMessage.encode message.sequencedMessage))

def decode (bytes : List UInt8) : Option (SequencedDataPacket × List UInt8) := do
  let (timestamp, bytes) ← Alpha.decode 8 bytes
  let (messageType, bytes) ← decodeUInt 1 bytes
  let (sequencedMessage, bytes) ← SequencedMessage.decode messageType bytes
  pure ({ timestamp, sequencedMessage }, bytes)

theorem encode_length_pos (message : SequencedDataPacket) : (encode message).length > 0 := by
  unfold encode
  simp only [Alpha.encode_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : SequencedDataPacket) : (encode message).length ≤ 61 := by
  unfold encode
  cases message.sequencedMessage with
  | systemEventMessage inner =>
    simp only [SequencedMessage.encode, List.length_append, ← Nat.add_assoc, Alpha.encode_length, encodeUInt_length, SystemEventMessage.encode_length]
    omega
  | stockStatusMessage inner =>
    simp only [SequencedMessage.encode, List.length_append, ← Nat.add_assoc, Alpha.encode_length, encodeUInt_length, StockStatusMessage.encode_length]
    omega
  | addOrderMessage inner =>
    simp only [SequencedMessage.encode, List.length_append, ← Nat.add_assoc, Alpha.encode_length, encodeUInt_length, AddOrderMessage.encode_length]
    omega
  | longFormAddOrderMessage inner =>
    simp only [SequencedMessage.encode, List.length_append, ← Nat.add_assoc, Alpha.encode_length, encodeUInt_length, LongFormAddOrderMessage.encode_length]
    omega

@[simp] theorem decode_encode (message : SequencedDataPacket) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [SequencedMessage.decode_encode, some_bind]
  rfl

end SequencedDataPacket

/-- Any Server Payload, selected by Server Packet Type -/
inductive ServerPayload where
  | debugPacket (message : DebugPacket) -- "+" 0x2B
  | loginAcceptedPacket (message : LoginAcceptedPacket) -- "A" 0x41
  | loginRejectedPacket (message : LoginRejectedPacket) -- "J" 0x4A
  | sequencedDataPacket (message : SequencedDataPacket) -- "S" 0x53
  deriving DecidableEq, Repr

namespace ServerPayload

/-- The Server Packet Type each message is sent under -/
def tag : ServerPayload → BitVec 8
  | .debugPacket _ => 43
  | .loginAcceptedPacket _ => 65
  | .loginRejectedPacket _ => 74
  | .sequencedDataPacket _ => 83

def encode : ServerPayload → List UInt8
  | .debugPacket message => DebugPacket.encode message
  | .loginAcceptedPacket message => LoginAcceptedPacket.encode message
  | .loginRejectedPacket message => LoginRejectedPacket.encode message
  | .sequencedDataPacket message => SequencedDataPacket.encode message

/-- The most bytes any message's encoding can take -/
theorem encode_length_le (message : ServerPayload) : (encode message).length ≤ 61 := by
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

def decode (tag : BitVec 8) (bytes : List UInt8) : Option (ServerPayload × List UInt8) :=
  if tag = 43 then (DebugPacket.decode bytes).map fun (message, rest) => (.debugPacket message, rest)
  else if tag = 65 then (LoginAcceptedPacket.decode bytes).map fun (message, rest) => (.loginAcceptedPacket message, rest)
  else if tag = 74 then (LoginRejectedPacket.decode bytes).map fun (message, rest) => (.loginRejectedPacket message, rest)
  else if tag = 83 then (SequencedDataPacket.decode bytes).map fun (message, rest) => (.sequencedDataPacket message, rest)
  else none

@[simp] theorem decode_encode (message : ServerPayload) (rest : List UInt8) :
    decode (tag message) (encode message ++ rest) = some (message, rest) := by
  cases message <;> simp [decode, encode, tag]

end ServerPayload

/-- Server Packet -/
structure ServerPacket where
  serverPayload : ServerPayload
  soupLf : BitVec 8
  deriving DecidableEq, Repr

namespace ServerPacket

def encode (message : ServerPacket) : List UInt8 :=
  encodeUInt 1 (ServerPayload.tag message.serverPayload)
    ++ (ServerPayload.encode message.serverPayload
    ++ (encodeUInt 1 message.soupLf))

def decode (bytes : List UInt8) : Option (ServerPacket × List UInt8) := do
  let (serverPacketType, bytes) ← decodeUInt 1 bytes
  let (serverPayload, bytes) ← ServerPayload.decode serverPacketType bytes
  let (soupLf, bytes) ← decodeUInt 1 bytes
  pure ({ serverPayload, soupLf }, bytes)

theorem encode_length_pos (message : ServerPacket) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUInt_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : ServerPacket) : (encode message).length ≤ 63 := by
  unfold encode
  cases message.serverPayload with
  | debugPacket inner =>
    simp only [ServerPayload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, DebugPacket.encode_length]
    omega
  | loginAcceptedPacket inner =>
    simp only [ServerPayload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, LoginAcceptedPacket.encode_length]
    omega
  | loginRejectedPacket inner =>
    simp only [ServerPayload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, LoginRejectedPacket.encode_length]
    omega
  | sequencedDataPacket inner =>
    have bound_inner := SequencedDataPacket.encode_length_le inner
    simp only [ServerPayload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length]
    omega

@[simp] theorem decode_encode (message : ServerPacket) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, ServerPayload.decode_encode, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end ServerPacket

end Omi.NasdaqNasdaqcanadaChixmmdGlimpseV10Server
