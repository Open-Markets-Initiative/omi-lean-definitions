import Omi.Wire

/-!
# Bolsa Institucional de Valores Total View v1.12

Generated from the binary model, with the proofs the model's rules call for: every record
decodes back to what was encoded; a message dispatch selects the message its type names;
a count is written from the list it counts; a length prefix is written from the bytes it frames;
and a packet read to the end of its data decodes to the messages that were written.

Note: Sequenced Data Packet is not framed: its length Packet Length is not an integer it reads.

Text fields are kept byte for byte, padding included, so what is decoded encodes back unchanged.
Prices with implied decimals are proven as the integers on the wire.
-/

namespace Omi.BivaBivaequitiesTotalviewGlimpseV112Server

/-- Event Code: one byte code -/
def EventCode.codes : List UInt8 :=
  [0x4F, 0x53, 0x51, 0x4D, 0x56, 0x55, 0x50, 0x54, 0x45, 0x43]

inductive EventCode where
  | startOfMessages -- Start Of Messages
  | startOfSystemHours -- Start Of System Hours
  | startOfMarketHours -- Start Of Market Hours
  | endOfMarketHours -- End Of Market Hours
  | scheduledAuctionStarts -- Scheduled Auction Starts
  | scheduledAuctionCloses -- Scheduled Auction Closes
  | startOfPostCloseSession -- Start Of Post Close Session
  | endOfPostCloseSession -- End Of Post Close Session
  | endOfSystemHours -- End Of System Hours
  | endOfMessages -- End Of Messages
  | unlisted (byte : { byte : UInt8 // byte ∉ EventCode.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace EventCode

def toByte : EventCode → UInt8
  | .startOfMessages => 0x4F
  | .startOfSystemHours => 0x53
  | .startOfMarketHours => 0x51
  | .endOfMarketHours => 0x4D
  | .scheduledAuctionStarts => 0x56
  | .scheduledAuctionCloses => 0x55
  | .startOfPostCloseSession => 0x50
  | .endOfPostCloseSession => 0x54
  | .endOfSystemHours => 0x45
  | .endOfMessages => 0x43
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : EventCode :=
  if byte = 0x4F then .startOfMessages
  else if byte = 0x53 then .startOfSystemHours
  else if byte = 0x51 then .startOfMarketHours
  else if byte = 0x4D then .endOfMarketHours
  else if byte = 0x56 then .scheduledAuctionStarts
  else if byte = 0x55 then .scheduledAuctionCloses
  else if byte = 0x50 then .startOfPostCloseSession
  else if byte = 0x54 then .endOfPostCloseSession
  else if byte = 0x45 then .endOfSystemHours
  else .endOfMessages

def ofByte (byte : UInt8) : EventCode :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : EventCode) : ofByte value.toByte = value := by
  cases value with
  | startOfMessages => decide
  | startOfSystemHours => decide
  | startOfMarketHours => decide
  | endOfMarketHours => decide
  | scheduledAuctionStarts => decide
  | scheduledAuctionCloses => decide
  | startOfPostCloseSession => decide
  | endOfPostCloseSession => decide
  | endOfSystemHours => decide
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

/-- Listing Type: one byte code -/
def ListingType.codes : List UInt8 :=
  [0x52, 0x53]

inductive ListingType where
  | regularSecurities -- Regular Securities
  | subRmSecurities -- Sub Rm Securities
  | unlisted (byte : { byte : UInt8 // byte ∉ ListingType.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace ListingType

def toByte : ListingType → UInt8
  | .regularSecurities => 0x52
  | .subRmSecurities => 0x53
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : ListingType :=
  if byte = 0x52 then .regularSecurities
  else .subRmSecurities

def ofByte (byte : UInt8) : ListingType :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : ListingType) : ofByte value.toByte = value := by
  cases value with
  | regularSecurities => decide
  | subRmSecurities => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : ListingType) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (ListingType × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : ListingType) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : ListingType) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end ListingType

/-- Trading State: one byte code -/
def TradingState.codes : List UInt8 :=
  [0x54, 0x56]

inductive TradingState where
  | trading -- Trading
  | suspended -- Suspended
  | unlisted (byte : { byte : UInt8 // byte ∉ TradingState.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace TradingState

def toByte : TradingState → UInt8
  | .trading => 0x54
  | .suspended => 0x56
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : TradingState :=
  if byte = 0x54 then .trading
  else .suspended

def ofByte (byte : UInt8) : TradingState :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : TradingState) : ofByte value.toByte = value := by
  cases value with
  | trading => decide
  | suspended => decide
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

/-- Trading Action Reason: one byte code -/
def TradingActionReason.codes : List UInt8 :=
  [0x4E, 0x48, 0x41, 0x42, 0x51, 0x53, 0x4D, 0x4F, 0x43, 0x49, 0x45, 0x4C]

inductive TradingActionReason where
  | normalTrading -- Normal Trading
  | volatilityAuction -- Volatility Auction
  | continuousAuctionStart -- Continuous Auction Start
  | continuousAuctionEnd -- Continuous Auction End
  | newsPending -- News Pending
  | staticPriceBandBreach -- Static Price Band Breach
  | marketSurveillanceSuspension -- Market Surveillance Suspension
  | suspensionByMarketOfOrigin -- Suspension By Market Of Origin
  | nonCompliance -- Non Compliance
  | startOfIndicationOfInterest -- Start Of Indication Of Interest
  | expiredSecurityIsUnavailableForTrading -- Expired Security Is Unavailable For Trading
  | notYetAvailableForTrading -- Not Yet Available For Trading
  | unlisted (byte : { byte : UInt8 // byte ∉ TradingActionReason.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace TradingActionReason

def toByte : TradingActionReason → UInt8
  | .normalTrading => 0x4E
  | .volatilityAuction => 0x48
  | .continuousAuctionStart => 0x41
  | .continuousAuctionEnd => 0x42
  | .newsPending => 0x51
  | .staticPriceBandBreach => 0x53
  | .marketSurveillanceSuspension => 0x4D
  | .suspensionByMarketOfOrigin => 0x4F
  | .nonCompliance => 0x43
  | .startOfIndicationOfInterest => 0x49
  | .expiredSecurityIsUnavailableForTrading => 0x45
  | .notYetAvailableForTrading => 0x4C
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : TradingActionReason :=
  if byte = 0x4E then .normalTrading
  else if byte = 0x48 then .volatilityAuction
  else if byte = 0x41 then .continuousAuctionStart
  else if byte = 0x42 then .continuousAuctionEnd
  else if byte = 0x51 then .newsPending
  else if byte = 0x53 then .staticPriceBandBreach
  else if byte = 0x4D then .marketSurveillanceSuspension
  else if byte = 0x4F then .suspensionByMarketOfOrigin
  else if byte = 0x43 then .nonCompliance
  else if byte = 0x49 then .startOfIndicationOfInterest
  else if byte = 0x45 then .expiredSecurityIsUnavailableForTrading
  else .notYetAvailableForTrading

def ofByte (byte : UInt8) : TradingActionReason :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : TradingActionReason) : ofByte value.toByte = value := by
  cases value with
  | normalTrading => decide
  | volatilityAuction => decide
  | continuousAuctionStart => decide
  | continuousAuctionEnd => decide
  | newsPending => decide
  | staticPriceBandBreach => decide
  | marketSurveillanceSuspension => decide
  | suspensionByMarketOfOrigin => decide
  | nonCompliance => decide
  | startOfIndicationOfInterest => decide
  | expiredSecurityIsUnavailableForTrading => decide
  | notYetAvailableForTrading => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : TradingActionReason) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (TradingActionReason × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : TradingActionReason) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : TradingActionReason) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end TradingActionReason

/-- Price Type: one byte code -/
def PriceType.codes : List UInt8 :=
  [0x43, 0x52, 0x49, 0x56]

inductive PriceType where
  | closePrice -- Close Price
  | referencePrice -- Reference Price
  | inav -- Inav
  | vwapOrPpp -- Vwap Or Ppp
  | unlisted (byte : { byte : UInt8 // byte ∉ PriceType.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace PriceType

def toByte : PriceType → UInt8
  | .closePrice => 0x43
  | .referencePrice => 0x52
  | .inav => 0x49
  | .vwapOrPpp => 0x56
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : PriceType :=
  if byte = 0x43 then .closePrice
  else if byte = 0x52 then .referencePrice
  else if byte = 0x49 then .inav
  else .vwapOrPpp

def ofByte (byte : UInt8) : PriceType :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : PriceType) : ofByte value.toByte = value := by
  cases value with
  | closePrice => decide
  | referencePrice => decide
  | inav => decide
  | vwapOrPpp => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : PriceType) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (PriceType × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : PriceType) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : PriceType) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end PriceType

/-- Reference Price Reason: one byte code -/
def ReferencePriceReason.codes : List UInt8 :=
  [0x20]

inductive ReferencePriceReason where
  | none_ -- None
  | unlisted (byte : { byte : UInt8 // byte ∉ ReferencePriceReason.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace ReferencePriceReason

def toByte : ReferencePriceReason → UInt8
  | .none_ => 0x20
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (_ : UInt8) : ReferencePriceReason :=
  .none_

def ofByte (byte : UInt8) : ReferencePriceReason :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : ReferencePriceReason) : ofByte value.toByte = value := by
  cases value with
  | none_ => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : ReferencePriceReason) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (ReferencePriceReason × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : ReferencePriceReason) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : ReferencePriceReason) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end ReferencePriceReason

/-- Order Verb: one byte code -/
def OrderVerb.codes : List UInt8 :=
  [0x42, 0x53]

inductive OrderVerb where
  | buy -- Buy
  | sell -- Sell
  | unlisted (byte : { byte : UInt8 // byte ∉ OrderVerb.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace OrderVerb

def toByte : OrderVerb → UInt8
  | .buy => 0x42
  | .sell => 0x53
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : OrderVerb :=
  if byte = 0x42 then .buy
  else .sell

def ofByte (byte : UInt8) : OrderVerb :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : OrderVerb) : ofByte value.toByte = value := by
  cases value with
  | buy => decide
  | sell => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : OrderVerb) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (OrderVerb × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : OrderVerb) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : OrderVerb) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end OrderVerb

/-- Cross Type: one byte code -/
def CrossType.codes : List UInt8 :=
  [0x4F, 0x49]

inductive CrossType where
  | preopeningSession -- Preopening Session
  | intradayAuction -- Intraday Auction
  | unlisted (byte : { byte : UInt8 // byte ∉ CrossType.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace CrossType

def toByte : CrossType → UInt8
  | .preopeningSession => 0x4F
  | .intradayAuction => 0x49
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : CrossType :=
  if byte = 0x4F then .preopeningSession
  else .intradayAuction

def ofByte (byte : UInt8) : CrossType :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : CrossType) : ofByte value.toByte = value := by
  cases value with
  | preopeningSession => decide
  | intradayAuction => decide
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

/-- Login Accepted Packet: 18 bytes -/
structure LoginAcceptedPacket where
  session : Alpha 10
  sequenceNumber : BitVec 64
  deriving DecidableEq, Repr

namespace LoginAcceptedPacket

def encode (message : LoginAcceptedPacket) : List UInt8 :=
  Alpha.encode message.session
    ++ (encodeUInt 8 message.sequenceNumber)

def decode (bytes : List UInt8) : Option (LoginAcceptedPacket × List UInt8) := do
  let (session, bytes) ← Alpha.decode 10 bytes
  let (sequenceNumber, bytes) ← decodeUInt 8 bytes
  pure ({ session, sequenceNumber }, bytes)

@[simp] theorem encode_length (message : LoginAcceptedPacket) : (encode message).length = 18 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length]

theorem encode_length_pos (message : LoginAcceptedPacket) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : LoginAcceptedPacket) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
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

/-- Time Stamp Seconds Message: 4 bytes -/
structure TimeStampSecondsMessage where
  second : BitVec 32
  deriving DecidableEq, Repr

namespace TimeStampSecondsMessage

def encode (message : TimeStampSecondsMessage) : List UInt8 :=
  encodeUInt 4 message.second

def decode (bytes : List UInt8) : Option (TimeStampSecondsMessage × List UInt8) := do
  let (second, bytes) ← decodeUInt 4 bytes
  pure ({ second }, bytes)

@[simp] theorem encode_length (message : TimeStampSecondsMessage) : (encode message).length = 4 := by
  unfold encode
  simp only [encodeUInt_length]

theorem encode_length_pos (message : TimeStampSecondsMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : TimeStampSecondsMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end TimeStampSecondsMessage

/-- System Event Message: 17 bytes -/
structure SystemEventMessage where
  nanoseconds : BitVec 32
  group : Alpha 8
  eventCode : EventCode
  orderbook : BitVec 32
  deriving DecidableEq, Repr

namespace SystemEventMessage

def encode (message : SystemEventMessage) : List UInt8 :=
  encodeUInt 4 message.nanoseconds
    ++ (Alpha.encode message.group
    ++ (EventCode.encode message.eventCode
    ++ (encodeUInt 4 message.orderbook)))

def decode (bytes : List UInt8) : Option (SystemEventMessage × List UInt8) := do
  let (nanoseconds, bytes) ← decodeUInt 4 bytes
  let (group, bytes) ← Alpha.decode 8 bytes
  let (eventCode, bytes) ← EventCode.decode bytes
  let (orderbook, bytes) ← decodeUInt 4 bytes
  pure ({ nanoseconds, group, eventCode, orderbook }, bytes)

@[simp] theorem encode_length (message : SystemEventMessage) : (encode message).length = 17 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Alpha.encode_length, EventCode.encode_length]

theorem encode_length_pos (message : SystemEventMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SystemEventMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, EventCode.decode_encode, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end SystemEventMessage

/-- Price Tick Size Message: 16 bytes -/
structure PriceTickSizeMessage where
  nanoseconds : BitVec 32
  tickSizeTableId : BitVec 32
  priceTickSize : BitVec 32
  priceStart : BitVec 32
  deriving DecidableEq, Repr

namespace PriceTickSizeMessage

def encode (message : PriceTickSizeMessage) : List UInt8 :=
  encodeUInt 4 message.nanoseconds
    ++ (encodeUInt 4 message.tickSizeTableId
    ++ (encodeUInt 4 message.priceTickSize
    ++ (encodeUInt 4 message.priceStart)))

def decode (bytes : List UInt8) : Option (PriceTickSizeMessage × List UInt8) := do
  let (nanoseconds, bytes) ← decodeUInt 4 bytes
  let (tickSizeTableId, bytes) ← decodeUInt 4 bytes
  let (priceTickSize, bytes) ← decodeUInt 4 bytes
  let (priceStart, bytes) ← decodeUInt 4 bytes
  pure ({ nanoseconds, tickSizeTableId, priceTickSize, priceStart }, bytes)

@[simp] theorem encode_length (message : PriceTickSizeMessage) : (encode message).length = 16 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length]

theorem encode_length_pos (message : PriceTickSizeMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : PriceTickSizeMessage) (rest : List UInt8) :
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

end PriceTickSizeMessage

/-- Quantity Tick Size Message: 24 bytes -/
structure QuantityTickSizeMessage where
  nanoseconds : BitVec 32
  tickSizeTableId : BitVec 32
  quantityTickSize : BitVec 64
  quantityStart : BitVec 64
  deriving DecidableEq, Repr

namespace QuantityTickSizeMessage

def encode (message : QuantityTickSizeMessage) : List UInt8 :=
  encodeUInt 4 message.nanoseconds
    ++ (encodeUInt 4 message.tickSizeTableId
    ++ (encodeUInt 8 message.quantityTickSize
    ++ (encodeUInt 8 message.quantityStart)))

def decode (bytes : List UInt8) : Option (QuantityTickSizeMessage × List UInt8) := do
  let (nanoseconds, bytes) ← decodeUInt 4 bytes
  let (tickSizeTableId, bytes) ← decodeUInt 4 bytes
  let (quantityTickSize, bytes) ← decodeUInt 8 bytes
  let (quantityStart, bytes) ← decodeUInt 8 bytes
  pure ({ nanoseconds, tickSizeTableId, quantityTickSize, quantityStart }, bytes)

@[simp] theorem encode_length (message : QuantityTickSizeMessage) : (encode message).length = 24 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length]

theorem encode_length_pos (message : QuantityTickSizeMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : QuantityTickSizeMessage) (rest : List UInt8) :
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

end QuantityTickSizeMessage

/-- Orderbook Directory Message: 99 bytes -/
structure OrderbookDirectoryMessage where
  nanoseconds : BitVec 32
  orderbook : BitVec 32
  isin : Alpha 12
  secCode : Alpha 15
  currency : Alpha 3
  group : Alpha 8
  minimumQuantity : BitVec 64
  quantityTickSizeTableId : BitVec 32
  quantityDecimals : BitVec 32
  priceTickSizeTableId : BitVec 32
  priceDecimals : BitVec 32
  delistingOrMaturityDate : BitVec 32
  delistingTime : BitVec 32
  turnoverRatio : Alpha 1
  quotationBasis : Alpha 3
  instrument : Alpha 12
  listingType : ListingType
  listingExchange : Alpha 4
  deriving DecidableEq, Repr

namespace OrderbookDirectoryMessage

def encode (message : OrderbookDirectoryMessage) : List UInt8 :=
  encodeUInt 4 message.nanoseconds
    ++ (encodeUInt 4 message.orderbook
    ++ (Alpha.encode message.isin
    ++ (Alpha.encode message.secCode
    ++ (Alpha.encode message.currency
    ++ (Alpha.encode message.group
    ++ (encodeUInt 8 message.minimumQuantity
    ++ (encodeUInt 4 message.quantityTickSizeTableId
    ++ (encodeUInt 4 message.quantityDecimals
    ++ (encodeUInt 4 message.priceTickSizeTableId
    ++ (encodeUInt 4 message.priceDecimals
    ++ (encodeUInt 4 message.delistingOrMaturityDate
    ++ (encodeUInt 4 message.delistingTime
    ++ (Alpha.encode message.turnoverRatio
    ++ (Alpha.encode message.quotationBasis
    ++ (Alpha.encode message.instrument
    ++ (ListingType.encode message.listingType
    ++ (Alpha.encode message.listingExchange)))))))))))))))))

def decode (bytes : List UInt8) : Option (OrderbookDirectoryMessage × List UInt8) := do
  let (nanoseconds, bytes) ← decodeUInt 4 bytes
  let (orderbook, bytes) ← decodeUInt 4 bytes
  let (isin, bytes) ← Alpha.decode 12 bytes
  let (secCode, bytes) ← Alpha.decode 15 bytes
  let (currency, bytes) ← Alpha.decode 3 bytes
  let (group, bytes) ← Alpha.decode 8 bytes
  let (minimumQuantity, bytes) ← decodeUInt 8 bytes
  let (quantityTickSizeTableId, bytes) ← decodeUInt 4 bytes
  let (quantityDecimals, bytes) ← decodeUInt 4 bytes
  let (priceTickSizeTableId, bytes) ← decodeUInt 4 bytes
  let (priceDecimals, bytes) ← decodeUInt 4 bytes
  let (delistingOrMaturityDate, bytes) ← decodeUInt 4 bytes
  let (delistingTime, bytes) ← decodeUInt 4 bytes
  let (turnoverRatio, bytes) ← Alpha.decode 1 bytes
  let (quotationBasis, bytes) ← Alpha.decode 3 bytes
  let (instrument, bytes) ← Alpha.decode 12 bytes
  let (listingType, bytes) ← ListingType.decode bytes
  let (listingExchange, bytes) ← Alpha.decode 4 bytes
  pure ({ nanoseconds, orderbook, isin, secCode, currency, group, minimumQuantity, quantityTickSizeTableId, quantityDecimals, priceTickSizeTableId, priceDecimals, delistingOrMaturityDate, delistingTime, turnoverRatio, quotationBasis, instrument, listingType, listingExchange }, bytes)

@[simp] theorem encode_length (message : OrderbookDirectoryMessage) : (encode message).length = 99 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Alpha.encode_length, ListingType.encode_length]

theorem encode_length_pos (message : OrderbookDirectoryMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OrderbookDirectoryMessage) (rest : List UInt8) :
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
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, ListingType.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end OrderbookDirectoryMessage

/-- Participant Directory Message: 20 bytes -/
structure ParticipantDirectoryMessage where
  nanoseconds : BitVec 32
  participantId : BitVec 32
  participantCode : Alpha 12
  deriving DecidableEq, Repr

namespace ParticipantDirectoryMessage

def encode (message : ParticipantDirectoryMessage) : List UInt8 :=
  encodeUInt 4 message.nanoseconds
    ++ (encodeUInt 4 message.participantId
    ++ (Alpha.encode message.participantCode))

def decode (bytes : List UInt8) : Option (ParticipantDirectoryMessage × List UInt8) := do
  let (nanoseconds, bytes) ← decodeUInt 4 bytes
  let (participantId, bytes) ← decodeUInt 4 bytes
  let (participantCode, bytes) ← Alpha.decode 12 bytes
  pure ({ nanoseconds, participantId, participantCode }, bytes)

@[simp] theorem encode_length (message : ParticipantDirectoryMessage) : (encode message).length = 20 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Alpha.encode_length]

theorem encode_length_pos (message : ParticipantDirectoryMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : ParticipantDirectoryMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end ParticipantDirectoryMessage

/-- Orderbook Trading Action Message: 10 bytes -/
structure OrderbookTradingActionMessage where
  nanoseconds : BitVec 32
  orderbook : BitVec 32
  tradingState : TradingState
  tradingActionReason : TradingActionReason
  deriving DecidableEq, Repr

namespace OrderbookTradingActionMessage

def encode (message : OrderbookTradingActionMessage) : List UInt8 :=
  encodeUInt 4 message.nanoseconds
    ++ (encodeUInt 4 message.orderbook
    ++ (TradingState.encode message.tradingState
    ++ (TradingActionReason.encode message.tradingActionReason)))

def decode (bytes : List UInt8) : Option (OrderbookTradingActionMessage × List UInt8) := do
  let (nanoseconds, bytes) ← decodeUInt 4 bytes
  let (orderbook, bytes) ← decodeUInt 4 bytes
  let (tradingState, bytes) ← TradingState.decode bytes
  let (tradingActionReason, bytes) ← TradingActionReason.decode bytes
  pure ({ nanoseconds, orderbook, tradingState, tradingActionReason }, bytes)

@[simp] theorem encode_length (message : OrderbookTradingActionMessage) : (encode message).length = 10 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, TradingState.encode_length, TradingActionReason.encode_length]

theorem encode_length_pos (message : OrderbookTradingActionMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OrderbookTradingActionMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, TradingState.decode_encode, some_bind]
  dsimp only
  rw [TradingActionReason.decode_encode, some_bind]
  rfl

end OrderbookTradingActionMessage

/-- Orderbook Reference Price Message: 14 bytes -/
structure OrderbookReferencePriceMessage where
  nanoseconds : BitVec 32
  orderbook : BitVec 32
  referencePrice : BitVec 32
  priceType : PriceType
  referencePriceReason : ReferencePriceReason
  deriving DecidableEq, Repr

namespace OrderbookReferencePriceMessage

def encode (message : OrderbookReferencePriceMessage) : List UInt8 :=
  encodeUInt 4 message.nanoseconds
    ++ (encodeUInt 4 message.orderbook
    ++ (encodeUInt 4 message.referencePrice
    ++ (PriceType.encode message.priceType
    ++ (ReferencePriceReason.encode message.referencePriceReason))))

def decode (bytes : List UInt8) : Option (OrderbookReferencePriceMessage × List UInt8) := do
  let (nanoseconds, bytes) ← decodeUInt 4 bytes
  let (orderbook, bytes) ← decodeUInt 4 bytes
  let (referencePrice, bytes) ← decodeUInt 4 bytes
  let (priceType, bytes) ← PriceType.decode bytes
  let (referencePriceReason, bytes) ← ReferencePriceReason.decode bytes
  pure ({ nanoseconds, orderbook, referencePrice, priceType, referencePriceReason }, bytes)

@[simp] theorem encode_length (message : OrderbookReferencePriceMessage) : (encode message).length = 14 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, PriceType.encode_length, ReferencePriceReason.encode_length]

theorem encode_length_pos (message : OrderbookReferencePriceMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OrderbookReferencePriceMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, PriceType.decode_encode, some_bind]
  dsimp only
  rw [ReferencePriceReason.decode_encode, some_bind]
  rfl

end OrderbookReferencePriceMessage

/-- Add Order Message: 33 bytes -/
structure AddOrderMessage where
  nanoseconds : BitVec 32
  orderNumber : BitVec 64
  orderVerb : OrderVerb
  quantity : BitVec 64
  orderbook : BitVec 32
  price : BitVec 32
  participantId : BitVec 32
  deriving DecidableEq, Repr

namespace AddOrderMessage

def encode (message : AddOrderMessage) : List UInt8 :=
  encodeUInt 4 message.nanoseconds
    ++ (encodeUInt 8 message.orderNumber
    ++ (OrderVerb.encode message.orderVerb
    ++ (encodeUInt 8 message.quantity
    ++ (encodeUInt 4 message.orderbook
    ++ (encodeUInt 4 message.price
    ++ (encodeUInt 4 message.participantId))))))

def decode (bytes : List UInt8) : Option (AddOrderMessage × List UInt8) := do
  let (nanoseconds, bytes) ← decodeUInt 4 bytes
  let (orderNumber, bytes) ← decodeUInt 8 bytes
  let (orderVerb, bytes) ← OrderVerb.decode bytes
  let (quantity, bytes) ← decodeUInt 8 bytes
  let (orderbook, bytes) ← decodeUInt 4 bytes
  let (price, bytes) ← decodeUInt 4 bytes
  let (participantId, bytes) ← decodeUInt 4 bytes
  pure ({ nanoseconds, orderNumber, orderVerb, quantity, orderbook, price, participantId }, bytes)

@[simp] theorem encode_length (message : AddOrderMessage) : (encode message).length = 33 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, OrderVerb.encode_length]

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
  rw [List.append_assoc, OrderVerb.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end AddOrderMessage

/-- Indicative Price Quantity Message: 29 bytes -/
structure IndicativePriceQuantityMessage where
  nanoseconds : BitVec 32
  theoreticalOpeningQuantity : BitVec 64
  orderbook : BitVec 32
  bestBid : BitVec 32
  bestOffer : BitVec 32
  theoreticalOpeningPrice : BitVec 32
  crossType : CrossType
  deriving DecidableEq, Repr

namespace IndicativePriceQuantityMessage

def encode (message : IndicativePriceQuantityMessage) : List UInt8 :=
  encodeUInt 4 message.nanoseconds
    ++ (encodeUInt 8 message.theoreticalOpeningQuantity
    ++ (encodeUInt 4 message.orderbook
    ++ (encodeUInt 4 message.bestBid
    ++ (encodeUInt 4 message.bestOffer
    ++ (encodeUInt 4 message.theoreticalOpeningPrice
    ++ (CrossType.encode message.crossType))))))

def decode (bytes : List UInt8) : Option (IndicativePriceQuantityMessage × List UInt8) := do
  let (nanoseconds, bytes) ← decodeUInt 4 bytes
  let (theoreticalOpeningQuantity, bytes) ← decodeUInt 8 bytes
  let (orderbook, bytes) ← decodeUInt 4 bytes
  let (bestBid, bytes) ← decodeUInt 4 bytes
  let (bestOffer, bytes) ← decodeUInt 4 bytes
  let (theoreticalOpeningPrice, bytes) ← decodeUInt 4 bytes
  let (crossType, bytes) ← CrossType.decode bytes
  pure ({ nanoseconds, theoreticalOpeningQuantity, orderbook, bestBid, bestOffer, theoreticalOpeningPrice, crossType }, bytes)

@[simp] theorem encode_length (message : IndicativePriceQuantityMessage) : (encode message).length = 29 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, CrossType.encode_length]

theorem encode_length_pos (message : IndicativePriceQuantityMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : IndicativePriceQuantityMessage) (rest : List UInt8) :
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
  rw [CrossType.decode_encode, some_bind]
  rfl

end IndicativePriceQuantityMessage

/-- Glimpse Snapshot Message: 8 bytes -/
structure GlimpseSnapshotMessage where
  sequenceNumber : BitVec 64
  deriving DecidableEq, Repr

namespace GlimpseSnapshotMessage

def encode (message : GlimpseSnapshotMessage) : List UInt8 :=
  encodeUInt 8 message.sequenceNumber

def decode (bytes : List UInt8) : Option (GlimpseSnapshotMessage × List UInt8) := do
  let (sequenceNumber, bytes) ← decodeUInt 8 bytes
  pure ({ sequenceNumber }, bytes)

@[simp] theorem encode_length (message : GlimpseSnapshotMessage) : (encode message).length = 8 := by
  unfold encode
  simp only [encodeUInt_length]

theorem encode_length_pos (message : GlimpseSnapshotMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : GlimpseSnapshotMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end GlimpseSnapshotMessage

/-- Any Sequenced Message, selected by Sequenced Message Type -/
inductive SequencedMessage where
  | timeStampSecondsMessage (message : TimeStampSecondsMessage) -- 'T' 0x54
  | systemEventMessage (message : SystemEventMessage) -- 'S' 0x53
  | priceTickSizeMessage (message : PriceTickSizeMessage) -- 'L' 0x4C
  | quantityTickSizeMessage (message : QuantityTickSizeMessage) -- 'M' 0x4D
  | orderbookDirectoryMessage (message : OrderbookDirectoryMessage) -- 'R' 0x52
  | participantDirectoryMessage (message : ParticipantDirectoryMessage) -- 'F' 0x46
  | orderbookTradingActionMessage (message : OrderbookTradingActionMessage) -- 'H' 0x48
  | orderbookReferencePriceMessage (message : OrderbookReferencePriceMessage) -- 'X' 0x58
  | addOrderMessage (message : AddOrderMessage) -- 'A' 0x41
  | indicativePriceQuantityMessage (message : IndicativePriceQuantityMessage) -- 'I' 0x49
  | glimpseSnapshotMessage (message : GlimpseSnapshotMessage) -- 'G' 0x47
  deriving DecidableEq, Repr

namespace SequencedMessage

/-- The Sequenced Message Type each message is sent under -/
def tag : SequencedMessage → BitVec 8
  | .timeStampSecondsMessage _ => 84
  | .systemEventMessage _ => 83
  | .priceTickSizeMessage _ => 76
  | .quantityTickSizeMessage _ => 77
  | .orderbookDirectoryMessage _ => 82
  | .participantDirectoryMessage _ => 70
  | .orderbookTradingActionMessage _ => 72
  | .orderbookReferencePriceMessage _ => 88
  | .addOrderMessage _ => 65
  | .indicativePriceQuantityMessage _ => 73
  | .glimpseSnapshotMessage _ => 71

def encode : SequencedMessage → List UInt8
  | .timeStampSecondsMessage message => TimeStampSecondsMessage.encode message
  | .systemEventMessage message => SystemEventMessage.encode message
  | .priceTickSizeMessage message => PriceTickSizeMessage.encode message
  | .quantityTickSizeMessage message => QuantityTickSizeMessage.encode message
  | .orderbookDirectoryMessage message => OrderbookDirectoryMessage.encode message
  | .participantDirectoryMessage message => ParticipantDirectoryMessage.encode message
  | .orderbookTradingActionMessage message => OrderbookTradingActionMessage.encode message
  | .orderbookReferencePriceMessage message => OrderbookReferencePriceMessage.encode message
  | .addOrderMessage message => AddOrderMessage.encode message
  | .indicativePriceQuantityMessage message => IndicativePriceQuantityMessage.encode message
  | .glimpseSnapshotMessage message => GlimpseSnapshotMessage.encode message

/-- The most bytes any message's encoding can take -/
theorem encode_length_le (message : SequencedMessage) : (encode message).length ≤ 99 := by
  cases message with
  | timeStampSecondsMessage inner =>
    simp only [encode, TimeStampSecondsMessage.encode_length]
    omega
  | systemEventMessage inner =>
    simp only [encode, SystemEventMessage.encode_length]
    omega
  | priceTickSizeMessage inner =>
    simp only [encode, PriceTickSizeMessage.encode_length]
    omega
  | quantityTickSizeMessage inner =>
    simp only [encode, QuantityTickSizeMessage.encode_length]
    omega
  | orderbookDirectoryMessage inner =>
    simp only [encode, OrderbookDirectoryMessage.encode_length]
    omega
  | participantDirectoryMessage inner =>
    simp only [encode, ParticipantDirectoryMessage.encode_length]
    omega
  | orderbookTradingActionMessage inner =>
    simp only [encode, OrderbookTradingActionMessage.encode_length]
    omega
  | orderbookReferencePriceMessage inner =>
    simp only [encode, OrderbookReferencePriceMessage.encode_length]
    omega
  | addOrderMessage inner =>
    simp only [encode, AddOrderMessage.encode_length]
    omega
  | indicativePriceQuantityMessage inner =>
    simp only [encode, IndicativePriceQuantityMessage.encode_length]
    omega
  | glimpseSnapshotMessage inner =>
    simp only [encode, GlimpseSnapshotMessage.encode_length]
    omega

def decode (tag : BitVec 8) (bytes : List UInt8) : Option (SequencedMessage × List UInt8) :=
  if tag = 84 then (TimeStampSecondsMessage.decode bytes).map fun (message, rest) => (.timeStampSecondsMessage message, rest)
  else if tag = 83 then (SystemEventMessage.decode bytes).map fun (message, rest) => (.systemEventMessage message, rest)
  else if tag = 76 then (PriceTickSizeMessage.decode bytes).map fun (message, rest) => (.priceTickSizeMessage message, rest)
  else if tag = 77 then (QuantityTickSizeMessage.decode bytes).map fun (message, rest) => (.quantityTickSizeMessage message, rest)
  else if tag = 82 then (OrderbookDirectoryMessage.decode bytes).map fun (message, rest) => (.orderbookDirectoryMessage message, rest)
  else if tag = 70 then (ParticipantDirectoryMessage.decode bytes).map fun (message, rest) => (.participantDirectoryMessage message, rest)
  else if tag = 72 then (OrderbookTradingActionMessage.decode bytes).map fun (message, rest) => (.orderbookTradingActionMessage message, rest)
  else if tag = 88 then (OrderbookReferencePriceMessage.decode bytes).map fun (message, rest) => (.orderbookReferencePriceMessage message, rest)
  else if tag = 65 then (AddOrderMessage.decode bytes).map fun (message, rest) => (.addOrderMessage message, rest)
  else if tag = 73 then (IndicativePriceQuantityMessage.decode bytes).map fun (message, rest) => (.indicativePriceQuantityMessage message, rest)
  else if tag = 71 then (GlimpseSnapshotMessage.decode bytes).map fun (message, rest) => (.glimpseSnapshotMessage message, rest)
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
theorem encode_length_le (message : SequencedDataPacket) : (encode message).length ≤ 100 := by
  unfold encode
  cases message.sequencedMessage with
  | timeStampSecondsMessage inner =>
    simp only [SequencedMessage.encode, List.length_append, encodeUInt_length, TimeStampSecondsMessage.encode_length]
    omega
  | systemEventMessage inner =>
    simp only [SequencedMessage.encode, List.length_append, encodeUInt_length, SystemEventMessage.encode_length]
    omega
  | priceTickSizeMessage inner =>
    simp only [SequencedMessage.encode, List.length_append, encodeUInt_length, PriceTickSizeMessage.encode_length]
    omega
  | quantityTickSizeMessage inner =>
    simp only [SequencedMessage.encode, List.length_append, encodeUInt_length, QuantityTickSizeMessage.encode_length]
    omega
  | orderbookDirectoryMessage inner =>
    simp only [SequencedMessage.encode, List.length_append, encodeUInt_length, OrderbookDirectoryMessage.encode_length]
    omega
  | participantDirectoryMessage inner =>
    simp only [SequencedMessage.encode, List.length_append, encodeUInt_length, ParticipantDirectoryMessage.encode_length]
    omega
  | orderbookTradingActionMessage inner =>
    simp only [SequencedMessage.encode, List.length_append, encodeUInt_length, OrderbookTradingActionMessage.encode_length]
    omega
  | orderbookReferencePriceMessage inner =>
    simp only [SequencedMessage.encode, List.length_append, encodeUInt_length, OrderbookReferencePriceMessage.encode_length]
    omega
  | addOrderMessage inner =>
    simp only [SequencedMessage.encode, List.length_append, encodeUInt_length, AddOrderMessage.encode_length]
    omega
  | indicativePriceQuantityMessage inner =>
    simp only [SequencedMessage.encode, List.length_append, encodeUInt_length, IndicativePriceQuantityMessage.encode_length]
    omega
  | glimpseSnapshotMessage inner =>
    simp only [SequencedMessage.encode, List.length_append, encodeUInt_length, GlimpseSnapshotMessage.encode_length]
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
theorem encode_length_le (message : ServerPayload) : (encode message).length ≤ 100 := by
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

end Omi.BivaBivaequitiesTotalviewGlimpseV112Server
