import Omi.Wire

/-!
# CIX Trading Inc. CIX Tcp Snapshot v1.1

Generated from the binary model, with the proofs the model's rules call for: every record
decodes back to what was encoded; a message dispatch selects the message its type names;
a count is written from the list it counts; a length prefix is written from the bytes it frames;
and a packet read to the end of its data decodes to the messages that were written.

Note: Binary Data Message is not framed: its length Length is not an integer it reads.

Text fields are kept byte for byte, padding included, so what is decoded encodes back unchanged.
Prices with implied decimals are proven as the integers on the wire.
-/

namespace Omi.CixatsCixaspenSnapshotTcpoutV11

/-- Feed Identifier: one byte code -/
def FeedIdentifier.codes : List UInt8 :=
  [0x41, 0x56, 0x4D, 0x42, 0x57, 0x4E]

inductive FeedIdentifier where
  | aspen -- Aspen
  | aspenVert -- Aspen Vert
  | midpoint -- Midpoint
  | aspenUat -- Aspen Uat
  | aspenVertUat -- Aspen Vert Uat
  | midpointUat -- Midpoint Uat
  | unlisted (byte : { byte : UInt8 // byte ∉ FeedIdentifier.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace FeedIdentifier

def toByte : FeedIdentifier → UInt8
  | .aspen => 0x41
  | .aspenVert => 0x56
  | .midpoint => 0x4D
  | .aspenUat => 0x42
  | .aspenVertUat => 0x57
  | .midpointUat => 0x4E
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : FeedIdentifier :=
  if byte = 0x41 then .aspen
  else if byte = 0x56 then .aspenVert
  else if byte = 0x4D then .midpoint
  else if byte = 0x42 then .aspenUat
  else if byte = 0x57 then .aspenVertUat
  else .midpointUat

def ofByte (byte : UInt8) : FeedIdentifier :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : FeedIdentifier) : ofByte value.toByte = value := by
  cases value with
  | aspen => decide
  | aspenVert => decide
  | midpoint => decide
  | aspenUat => decide
  | aspenVertUat => decide
  | midpointUat => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : FeedIdentifier) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (FeedIdentifier × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : FeedIdentifier) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : FeedIdentifier) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end FeedIdentifier

/-- Reason Code: one byte code -/
def ReasonCode.codes : List UInt8 :=
  [0x41, 0x42, 0x53]

inductive ReasonCode where
  | invalidUserPassword -- Invalid User Password
  | invalidSequence -- Invalid Sequence
  | invalidMarketDayFeedId -- Invalid Market Day Feed Id
  | unlisted (byte : { byte : UInt8 // byte ∉ ReasonCode.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace ReasonCode

def toByte : ReasonCode → UInt8
  | .invalidUserPassword => 0x41
  | .invalidSequence => 0x42
  | .invalidMarketDayFeedId => 0x53
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : ReasonCode :=
  if byte = 0x41 then .invalidUserPassword
  else if byte = 0x42 then .invalidSequence
  else .invalidMarketDayFeedId

def ofByte (byte : UInt8) : ReasonCode :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : ReasonCode) : ofByte value.toByte = value := by
  cases value with
  | invalidUserPassword => decide
  | invalidSequence => decide
  | invalidMarketDayFeedId => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : ReasonCode) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (ReasonCode × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : ReasonCode) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : ReasonCode) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end ReasonCode

/-- Event: one byte code -/
def Event.codes : List UInt8 :=
  [0x4F, 0x53, 0x51, 0x45, 0x43]

inductive Event where
  | startOfSession -- Start Of Session
  | marketAcceptingOrders -- Market Accepting Orders
  | marketOpenForTrading -- Market Open For Trading
  | marketClosedForTrading -- Market Closed For Trading
  | endOfSession -- End Of Session
  | unlisted (byte : { byte : UInt8 // byte ∉ Event.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace Event

def toByte : Event → UInt8
  | .startOfSession => 0x4F
  | .marketAcceptingOrders => 0x53
  | .marketOpenForTrading => 0x51
  | .marketClosedForTrading => 0x45
  | .endOfSession => 0x43
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : Event :=
  if byte = 0x4F then .startOfSession
  else if byte = 0x53 then .marketAcceptingOrders
  else if byte = 0x51 then .marketOpenForTrading
  else if byte = 0x45 then .marketClosedForTrading
  else .endOfSession

def ofByte (byte : UInt8) : Event :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : Event) : ofByte value.toByte = value := by
  cases value with
  | startOfSession => decide
  | marketAcceptingOrders => decide
  | marketOpenForTrading => decide
  | marketClosedForTrading => decide
  | endOfSession => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : Event) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (Event × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : Event) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : Event) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end Event

/-- Listing Market: one byte code -/
def ListingMarket.codes : List UInt8 :=
  [0x54, 0x56, 0x43, 0x4E]

inductive ListingMarket where
  | tsx -- Tsx
  | venture -- Venture
  | cse -- Cse
  | neo -- Neo
  | unlisted (byte : { byte : UInt8 // byte ∉ ListingMarket.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace ListingMarket

def toByte : ListingMarket → UInt8
  | .tsx => 0x54
  | .venture => 0x56
  | .cse => 0x43
  | .neo => 0x4E
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : ListingMarket :=
  if byte = 0x54 then .tsx
  else if byte = 0x56 then .venture
  else if byte = 0x43 then .cse
  else .neo

def ofByte (byte : UInt8) : ListingMarket :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : ListingMarket) : ofByte value.toByte = value := by
  cases value with
  | tsx => decide
  | venture => decide
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

/-- State: one byte code -/
def State.codes : List UInt8 :=
  [0x48, 0x54]

inductive State where
  | halted -- Halted
  | trading -- Trading
  | unlisted (byte : { byte : UInt8 // byte ∉ State.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace State

def toByte : State → UInt8
  | .halted => 0x48
  | .trading => 0x54
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : State :=
  if byte = 0x48 then .halted
  else .trading

def ofByte (byte : UInt8) : State :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : State) : ofByte value.toByte = value := by
  cases value with
  | halted => decide
  | trading => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : State) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (State × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : State) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : State) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end State

/-- Side: one byte code -/
def Side.codes : List UInt8 :=
  [0x42, 0x53]

inductive Side where
  | buy -- Buy
  | sell -- Sell
  | unlisted (byte : { byte : UInt8 // byte ∉ Side.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace Side

def toByte : Side → UInt8
  | .buy => 0x42
  | .sell => 0x53
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : Side :=
  if byte = 0x42 then .buy
  else .sell

def ofByte (byte : UInt8) : Side :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : Side) : ofByte value.toByte = value := by
  cases value with
  | buy => decide
  | sell => decide
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

/-- Login Message: 46 bytes -/
structure LoginMessage where
  user : Alpha 6
  pass : Alpha 10
  marketDayIdentifier : Alpha 9
  feedIdentifier : FeedIdentifier
  requestedSequence : Alpha 20
  deriving DecidableEq, Repr

namespace LoginMessage

def encode (message : LoginMessage) : List UInt8 :=
  Alpha.encode message.user
    ++ (Alpha.encode message.pass
    ++ (Alpha.encode message.marketDayIdentifier
    ++ (FeedIdentifier.encode message.feedIdentifier
    ++ (Alpha.encode message.requestedSequence))))

def decode (bytes : List UInt8) : Option (LoginMessage × List UInt8) := do
  let (user, bytes) ← Alpha.decode 6 bytes
  let (pass, bytes) ← Alpha.decode 10 bytes
  let (marketDayIdentifier, bytes) ← Alpha.decode 9 bytes
  let (feedIdentifier, bytes) ← FeedIdentifier.decode bytes
  let (requestedSequence, bytes) ← Alpha.decode 20 bytes
  pure ({ user, pass, marketDayIdentifier, feedIdentifier, requestedSequence }, bytes)

@[simp] theorem encode_length (message : LoginMessage) : (encode message).length = 46 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, FeedIdentifier.encode_length]

theorem encode_length_pos (message : LoginMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : LoginMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, FeedIdentifier.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end LoginMessage

/-- Client Heartbeat Message: 0 bytes -/
structure ClientHeartbeatMessage where
  deriving DecidableEq, Repr

namespace ClientHeartbeatMessage

def encode (_ : ClientHeartbeatMessage) : List UInt8 :=
  []

def decode (bytes : List UInt8) : Option (ClientHeartbeatMessage × List UInt8) :=
  some (⟨⟩, bytes)

@[simp] theorem encode_length (message : ClientHeartbeatMessage) : (encode message).length = 0 := by
  simp [encode]

@[simp] theorem decode_encode (message : ClientHeartbeatMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  simp [decode, encode]

end ClientHeartbeatMessage

/-- Successful Login Message: 30 bytes -/
structure SuccessfulLoginMessage where
  marketDayIdentifier : Alpha 9
  feedIdentifier : FeedIdentifier
  nextSequence : Alpha 20
  deriving DecidableEq, Repr

namespace SuccessfulLoginMessage

def encode (message : SuccessfulLoginMessage) : List UInt8 :=
  Alpha.encode message.marketDayIdentifier
    ++ (FeedIdentifier.encode message.feedIdentifier
    ++ (Alpha.encode message.nextSequence))

def decode (bytes : List UInt8) : Option (SuccessfulLoginMessage × List UInt8) := do
  let (marketDayIdentifier, bytes) ← Alpha.decode 9 bytes
  let (feedIdentifier, bytes) ← FeedIdentifier.decode bytes
  let (nextSequence, bytes) ← Alpha.decode 20 bytes
  pure ({ marketDayIdentifier, feedIdentifier, nextSequence }, bytes)

@[simp] theorem encode_length (message : SuccessfulLoginMessage) : (encode message).length = 30 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, FeedIdentifier.encode_length]

theorem encode_length_pos (message : SuccessfulLoginMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SuccessfulLoginMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, FeedIdentifier.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end SuccessfulLoginMessage

/-- Login Reject Message: 1 bytes -/
structure LoginRejectMessage where
  reasonCode : ReasonCode
  deriving DecidableEq, Repr

namespace LoginRejectMessage

def encode (message : LoginRejectMessage) : List UInt8 :=
  ReasonCode.encode message.reasonCode

def decode (bytes : List UInt8) : Option (LoginRejectMessage × List UInt8) := do
  let (reasonCode, bytes) ← ReasonCode.decode bytes
  pure ({ reasonCode }, bytes)

@[simp] theorem encode_length (message : LoginRejectMessage) : (encode message).length = 1 := by
  unfold encode
  simp only [ReasonCode.encode_length]

theorem encode_length_pos (message : LoginRejectMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : LoginRejectMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [ReasonCode.decode_encode, some_bind]
  rfl

end LoginRejectMessage

/-- Server Heartbeat Message: 0 bytes -/
structure ServerHeartbeatMessage where
  deriving DecidableEq, Repr

namespace ServerHeartbeatMessage

def encode (_ : ServerHeartbeatMessage) : List UInt8 :=
  []

def decode (bytes : List UInt8) : Option (ServerHeartbeatMessage × List UInt8) :=
  some (⟨⟩, bytes)

@[simp] theorem encode_length (message : ServerHeartbeatMessage) : (encode message).length = 0 := by
  simp [encode]

@[simp] theorem decode_encode (message : ServerHeartbeatMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  simp [decode, encode]

end ServerHeartbeatMessage

/-- Market Event Message: 11 bytes -/
structure MarketEventMessage where
  reserved2 : Alpha 2
  timestamp : BitVec 64
  event : Event
  deriving DecidableEq, Repr

namespace MarketEventMessage

def encode (message : MarketEventMessage) : List UInt8 :=
  Alpha.encode message.reserved2
    ++ (encodeUIntLE 8 message.timestamp
    ++ (Event.encode message.event))

def decode (bytes : List UInt8) : Option (MarketEventMessage × List UInt8) := do
  let (reserved2, bytes) ← Alpha.decode 2 bytes
  let (timestamp, bytes) ← decodeUIntLE 8 bytes
  let (event, bytes) ← Event.decode bytes
  pure ({ reserved2, timestamp, event }, bytes)

@[simp] theorem encode_length (message : MarketEventMessage) : (encode message).length = 11 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUIntLE_length, Event.encode_length]

theorem encode_length_pos (message : MarketEventMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : MarketEventMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [Event.decode_encode, some_bind]
  rfl

end MarketEventMessage

/-- Symbol Information Message: 26 bytes -/
structure SymbolInformationMessage where
  timestamp : BitVec 64
  symbolId : BitVec 16
  symbol : Alpha 11
  listingMarket : ListingMarket
  boardLotSize : BitVec 32
  deriving DecidableEq, Repr

namespace SymbolInformationMessage

def encode (message : SymbolInformationMessage) : List UInt8 :=
  encodeUIntLE 8 message.timestamp
    ++ (encodeUIntLE 2 message.symbolId
    ++ (Alpha.encode message.symbol
    ++ (ListingMarket.encode message.listingMarket
    ++ (encodeUIntLE 4 message.boardLotSize))))

def decode (bytes : List UInt8) : Option (SymbolInformationMessage × List UInt8) := do
  let (timestamp, bytes) ← decodeUIntLE 8 bytes
  let (symbolId, bytes) ← decodeUIntLE 2 bytes
  let (symbol, bytes) ← Alpha.decode 11 bytes
  let (listingMarket, bytes) ← ListingMarket.decode bytes
  let (boardLotSize, bytes) ← decodeUIntLE 4 bytes
  pure ({ timestamp, symbolId, symbol, listingMarket, boardLotSize }, bytes)

@[simp] theorem encode_length (message : SymbolInformationMessage) : (encode message).length = 26 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length, ListingMarket.encode_length]

theorem encode_length_pos (message : SymbolInformationMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SymbolInformationMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, ListingMarket.decode_encode, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end SymbolInformationMessage

/-- Symbol State Message: 27 bytes -/
structure SymbolStateMessage where
  timestamp : BitVec 64
  symbolId : BitVec 16
  symbol : Alpha 11
  state : State
  reserved1 : Alpha 1
  info : Alpha 4
  deriving DecidableEq, Repr

namespace SymbolStateMessage

def encode (message : SymbolStateMessage) : List UInt8 :=
  encodeUIntLE 8 message.timestamp
    ++ (encodeUIntLE 2 message.symbolId
    ++ (Alpha.encode message.symbol
    ++ (State.encode message.state
    ++ (Alpha.encode message.reserved1
    ++ (Alpha.encode message.info)))))

def decode (bytes : List UInt8) : Option (SymbolStateMessage × List UInt8) := do
  let (timestamp, bytes) ← decodeUIntLE 8 bytes
  let (symbolId, bytes) ← decodeUIntLE 2 bytes
  let (symbol, bytes) ← Alpha.decode 11 bytes
  let (state, bytes) ← State.decode bytes
  let (reserved1, bytes) ← Alpha.decode 1 bytes
  let (info, bytes) ← Alpha.decode 4 bytes
  pure ({ timestamp, symbolId, symbol, state, reserved1, info }, bytes)

@[simp] theorem encode_length (message : SymbolStateMessage) : (encode message).length = 27 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length, State.encode_length]

theorem encode_length_pos (message : SymbolStateMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SymbolStateMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, State.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end SymbolStateMessage

/-- New Order Add Message: 50 bytes -/
structure NewOrderAddMessage where
  timestamp : BitVec 64
  symbolId : BitVec 16
  orderId : BitVec 64
  side : Side
  quantity : BitVec 64
  symbol : Alpha 11
  price : BitVec 64
  broker : Alpha 3
  reserved1 : Alpha 1
  deriving DecidableEq, Repr

namespace NewOrderAddMessage

def encode (message : NewOrderAddMessage) : List UInt8 :=
  encodeUIntLE 8 message.timestamp
    ++ (encodeUIntLE 2 message.symbolId
    ++ (encodeUIntLE 8 message.orderId
    ++ (Side.encode message.side
    ++ (encodeUIntLE 8 message.quantity
    ++ (Alpha.encode message.symbol
    ++ (encodeUIntLE 8 message.price
    ++ (Alpha.encode message.broker
    ++ (Alpha.encode message.reserved1))))))))

def decode (bytes : List UInt8) : Option (NewOrderAddMessage × List UInt8) := do
  let (timestamp, bytes) ← decodeUIntLE 8 bytes
  let (symbolId, bytes) ← decodeUIntLE 2 bytes
  let (orderId, bytes) ← decodeUIntLE 8 bytes
  let (side, bytes) ← Side.decode bytes
  let (quantity, bytes) ← decodeUIntLE 8 bytes
  let (symbol, bytes) ← Alpha.decode 11 bytes
  let (price, bytes) ← decodeUIntLE 8 bytes
  let (broker, bytes) ← Alpha.decode 3 bytes
  let (reserved1, bytes) ← Alpha.decode 1 bytes
  pure ({ timestamp, symbolId, orderId, side, quantity, symbol, price, broker, reserved1 }, bytes)

@[simp] theorem encode_length (message : NewOrderAddMessage) : (encode message).length = 50 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Side.encode_length, Alpha.encode_length]

theorem encode_length_pos (message : NewOrderAddMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : NewOrderAddMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Side.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end NewOrderAddMessage

/-- Order Partial Cancel Message: 24 bytes -/
structure OrderPartialCancelMessage where
  timestamp : BitVec 64
  orderId : BitVec 64
  quantityCanceled : BitVec 64
  deriving DecidableEq, Repr

namespace OrderPartialCancelMessage

def encode (message : OrderPartialCancelMessage) : List UInt8 :=
  encodeUIntLE 8 message.timestamp
    ++ (encodeUIntLE 8 message.orderId
    ++ (encodeUIntLE 8 message.quantityCanceled))

def decode (bytes : List UInt8) : Option (OrderPartialCancelMessage × List UInt8) := do
  let (timestamp, bytes) ← decodeUIntLE 8 bytes
  let (orderId, bytes) ← decodeUIntLE 8 bytes
  let (quantityCanceled, bytes) ← decodeUIntLE 8 bytes
  pure ({ timestamp, orderId, quantityCanceled }, bytes)

@[simp] theorem encode_length (message : OrderPartialCancelMessage) : (encode message).length = 24 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length]

theorem encode_length_pos (message : OrderPartialCancelMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OrderPartialCancelMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end OrderPartialCancelMessage

/-- Order Cancel All Message: 16 bytes -/
structure OrderCancelAllMessage where
  timestamp : BitVec 64
  orderId : BitVec 64
  deriving DecidableEq, Repr

namespace OrderCancelAllMessage

def encode (message : OrderCancelAllMessage) : List UInt8 :=
  encodeUIntLE 8 message.timestamp
    ++ (encodeUIntLE 8 message.orderId)

def decode (bytes : List UInt8) : Option (OrderCancelAllMessage × List UInt8) := do
  let (timestamp, bytes) ← decodeUIntLE 8 bytes
  let (orderId, bytes) ← decodeUIntLE 8 bytes
  pure ({ timestamp, orderId }, bytes)

@[simp] theorem encode_length (message : OrderCancelAllMessage) : (encode message).length = 16 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length]

theorem encode_length_pos (message : OrderCancelAllMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OrderCancelAllMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end OrderCancelAllMessage

/-- Order Executed Message: 47 bytes -/
structure OrderExecutedMessage where
  timestamp : BitVec 64
  orderId : BitVec 64
  quantity : BitVec 64
  executionId : BitVec 64
  side : Side
  price : BitVec 64
  broker : Alpha 3
  contraBroker : Alpha 3
  deriving DecidableEq, Repr

namespace OrderExecutedMessage

def encode (message : OrderExecutedMessage) : List UInt8 :=
  encodeUIntLE 8 message.timestamp
    ++ (encodeUIntLE 8 message.orderId
    ++ (encodeUIntLE 8 message.quantity
    ++ (encodeUIntLE 8 message.executionId
    ++ (Side.encode message.side
    ++ (encodeUIntLE 8 message.price
    ++ (Alpha.encode message.broker
    ++ (Alpha.encode message.contraBroker)))))))

def decode (bytes : List UInt8) : Option (OrderExecutedMessage × List UInt8) := do
  let (timestamp, bytes) ← decodeUIntLE 8 bytes
  let (orderId, bytes) ← decodeUIntLE 8 bytes
  let (quantity, bytes) ← decodeUIntLE 8 bytes
  let (executionId, bytes) ← decodeUIntLE 8 bytes
  let (side, bytes) ← Side.decode bytes
  let (price, bytes) ← decodeUIntLE 8 bytes
  let (broker, bytes) ← Alpha.decode 3 bytes
  let (contraBroker, bytes) ← Alpha.decode 3 bytes
  pure ({ timestamp, orderId, quantity, executionId, side, price, broker, contraBroker }, bytes)

@[simp] theorem encode_length (message : OrderExecutedMessage) : (encode message).length = 47 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Side.encode_length, Alpha.encode_length]

theorem encode_length_pos (message : OrderExecutedMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OrderExecutedMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Side.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end OrderExecutedMessage

/-- End Of Snapshot Message: 8 bytes -/
structure EndOfSnapshotMessage where
  sequence : BitVec 64
  deriving DecidableEq, Repr

namespace EndOfSnapshotMessage

def encode (message : EndOfSnapshotMessage) : List UInt8 :=
  encodeUIntLE 8 message.sequence

def decode (bytes : List UInt8) : Option (EndOfSnapshotMessage × List UInt8) := do
  let (sequence, bytes) ← decodeUIntLE 8 bytes
  pure ({ sequence }, bytes)

@[simp] theorem encode_length (message : EndOfSnapshotMessage) : (encode message).length = 8 := by
  unfold encode
  simp only [encodeUIntLE_length]

theorem encode_length_pos (message : EndOfSnapshotMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : EndOfSnapshotMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end EndOfSnapshotMessage

/-- Any Payload, selected by Message Type -/
inductive Payload where
  | marketEventMessage (message : MarketEventMessage) -- "A" 0x41
  | symbolInformationMessage (message : SymbolInformationMessage) -- "B" 0x42
  | symbolStateMessage (message : SymbolStateMessage) -- "C" 0x43
  | newOrderAddMessage (message : NewOrderAddMessage) -- "D" 0x44
  | orderPartialCancelMessage (message : OrderPartialCancelMessage) -- "F" 0x46
  | orderCancelAllMessage (message : OrderCancelAllMessage) -- "G" 0x47
  | orderExecutedMessage (message : OrderExecutedMessage) -- "J" 0x4A
  | endOfSnapshotMessage (message : EndOfSnapshotMessage) -- "X" 0x58
  deriving DecidableEq, Repr

namespace Payload

/-- The Message Type each message is sent under -/
def tag : Payload → BitVec 8
  | .marketEventMessage _ => 65
  | .symbolInformationMessage _ => 66
  | .symbolStateMessage _ => 67
  | .newOrderAddMessage _ => 68
  | .orderPartialCancelMessage _ => 70
  | .orderCancelAllMessage _ => 71
  | .orderExecutedMessage _ => 74
  | .endOfSnapshotMessage _ => 88

def encode : Payload → List UInt8
  | .marketEventMessage message => MarketEventMessage.encode message
  | .symbolInformationMessage message => SymbolInformationMessage.encode message
  | .symbolStateMessage message => SymbolStateMessage.encode message
  | .newOrderAddMessage message => NewOrderAddMessage.encode message
  | .orderPartialCancelMessage message => OrderPartialCancelMessage.encode message
  | .orderCancelAllMessage message => OrderCancelAllMessage.encode message
  | .orderExecutedMessage message => OrderExecutedMessage.encode message
  | .endOfSnapshotMessage message => EndOfSnapshotMessage.encode message

/-- The most bytes any message's encoding can take -/
theorem encode_length_le (message : Payload) : (encode message).length ≤ 50 := by
  cases message with
  | marketEventMessage inner =>
    simp only [encode, MarketEventMessage.encode_length]
    omega
  | symbolInformationMessage inner =>
    simp only [encode, SymbolInformationMessage.encode_length]
    omega
  | symbolStateMessage inner =>
    simp only [encode, SymbolStateMessage.encode_length]
    omega
  | newOrderAddMessage inner =>
    simp only [encode, NewOrderAddMessage.encode_length]
    omega
  | orderPartialCancelMessage inner =>
    simp only [encode, OrderPartialCancelMessage.encode_length]
    omega
  | orderCancelAllMessage inner =>
    simp only [encode, OrderCancelAllMessage.encode_length]
    omega
  | orderExecutedMessage inner =>
    simp only [encode, OrderExecutedMessage.encode_length]
    omega
  | endOfSnapshotMessage inner =>
    simp only [encode, EndOfSnapshotMessage.encode_length]
    omega

def decode (tag : BitVec 8) (bytes : List UInt8) : Option (Payload × List UInt8) :=
  if tag = 65 then (MarketEventMessage.decode bytes).map fun (message, rest) => (.marketEventMessage message, rest)
  else if tag = 66 then (SymbolInformationMessage.decode bytes).map fun (message, rest) => (.symbolInformationMessage message, rest)
  else if tag = 67 then (SymbolStateMessage.decode bytes).map fun (message, rest) => (.symbolStateMessage message, rest)
  else if tag = 68 then (NewOrderAddMessage.decode bytes).map fun (message, rest) => (.newOrderAddMessage message, rest)
  else if tag = 70 then (OrderPartialCancelMessage.decode bytes).map fun (message, rest) => (.orderPartialCancelMessage message, rest)
  else if tag = 71 then (OrderCancelAllMessage.decode bytes).map fun (message, rest) => (.orderCancelAllMessage message, rest)
  else if tag = 74 then (OrderExecutedMessage.decode bytes).map fun (message, rest) => (.orderExecutedMessage message, rest)
  else if tag = 88 then (EndOfSnapshotMessage.decode bytes).map fun (message, rest) => (.endOfSnapshotMessage message, rest)
  else none

@[simp] theorem decode_encode (message : Payload) (rest : List UInt8) :
    decode (tag message) (encode message ++ rest) = some (message, rest) := by
  cases message <;> simp [decode, encode, tag]

end Payload

/-- Binary Data Message -/
structure BinaryDataMessage where
  payload : Payload
  deriving DecidableEq, Repr

namespace BinaryDataMessage

def encode (message : BinaryDataMessage) : List UInt8 :=
  encodeUInt 1 (Payload.tag message.payload)
    ++ (Payload.encode message.payload)

def decode (bytes : List UInt8) : Option (BinaryDataMessage × List UInt8) := do
  let (messageType, bytes) ← decodeUInt 1 bytes
  let (payload, bytes) ← Payload.decode messageType bytes
  pure ({ payload }, bytes)

theorem encode_length_pos (message : BinaryDataMessage) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUInt_length, List.length_append]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : BinaryDataMessage) : (encode message).length ≤ 51 := by
  unfold encode
  cases message.payload with
  | marketEventMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, MarketEventMessage.encode_length]
    omega
  | symbolInformationMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, SymbolInformationMessage.encode_length]
    omega
  | symbolStateMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, SymbolStateMessage.encode_length]
    omega
  | newOrderAddMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, NewOrderAddMessage.encode_length]
    omega
  | orderPartialCancelMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, OrderPartialCancelMessage.encode_length]
    omega
  | orderCancelAllMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, OrderCancelAllMessage.encode_length]
    omega
  | orderExecutedMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, OrderExecutedMessage.encode_length]
    omega
  | endOfSnapshotMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, EndOfSnapshotMessage.encode_length]
    omega

@[simp] theorem decode_encode (message : BinaryDataMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [Payload.decode_encode, some_bind]
  rfl

end BinaryDataMessage

/-- Any Packet Payload, selected by Packet Type -/
inductive PacketPayload where
  | loginMessage (message : LoginMessage) -- "L" 0x4C
  | clientHeartbeatMessage (message : ClientHeartbeatMessage) -- "R" 0x52
  | successfulLoginMessage (message : SuccessfulLoginMessage) -- "A" 0x41
  | loginRejectMessage (message : LoginRejectMessage) -- "J" 0x4A
  | serverHeartbeatMessage (message : ServerHeartbeatMessage) -- "H" 0x48
  | binaryDataMessage (message : BinaryDataMessage) -- "S" 0x53
  deriving DecidableEq, Repr

namespace PacketPayload

/-- The Packet Type each message is sent under -/
def tag : PacketPayload → BitVec 8
  | .loginMessage _ => 76
  | .clientHeartbeatMessage _ => 82
  | .successfulLoginMessage _ => 65
  | .loginRejectMessage _ => 74
  | .serverHeartbeatMessage _ => 72
  | .binaryDataMessage _ => 83

def encode : PacketPayload → List UInt8
  | .loginMessage message => LoginMessage.encode message
  | .clientHeartbeatMessage message => ClientHeartbeatMessage.encode message
  | .successfulLoginMessage message => SuccessfulLoginMessage.encode message
  | .loginRejectMessage message => LoginRejectMessage.encode message
  | .serverHeartbeatMessage message => ServerHeartbeatMessage.encode message
  | .binaryDataMessage message => BinaryDataMessage.encode message

/-- The most bytes any message's encoding can take -/
theorem encode_length_le (message : PacketPayload) : (encode message).length ≤ 51 := by
  cases message with
  | loginMessage inner =>
    simp only [encode, LoginMessage.encode_length]
    omega
  | clientHeartbeatMessage inner =>
    simp only [encode, ClientHeartbeatMessage.encode_length]
    omega
  | successfulLoginMessage inner =>
    simp only [encode, SuccessfulLoginMessage.encode_length]
    omega
  | loginRejectMessage inner =>
    simp only [encode, LoginRejectMessage.encode_length]
    omega
  | serverHeartbeatMessage inner =>
    simp only [encode, ServerHeartbeatMessage.encode_length]
    omega
  | binaryDataMessage inner =>
    have bound_inner := BinaryDataMessage.encode_length_le inner
    simp only [encode]
    omega

def decode (tag : BitVec 8) (bytes : List UInt8) : Option (PacketPayload × List UInt8) :=
  if tag = 76 then (LoginMessage.decode bytes).map fun (message, rest) => (.loginMessage message, rest)
  else if tag = 82 then (ClientHeartbeatMessage.decode bytes).map fun (message, rest) => (.clientHeartbeatMessage message, rest)
  else if tag = 65 then (SuccessfulLoginMessage.decode bytes).map fun (message, rest) => (.successfulLoginMessage message, rest)
  else if tag = 74 then (LoginRejectMessage.decode bytes).map fun (message, rest) => (.loginRejectMessage message, rest)
  else if tag = 72 then (ServerHeartbeatMessage.decode bytes).map fun (message, rest) => (.serverHeartbeatMessage message, rest)
  else if tag = 83 then (BinaryDataMessage.decode bytes).map fun (message, rest) => (.binaryDataMessage message, rest)
  else none

@[simp] theorem decode_encode (message : PacketPayload) (rest : List UInt8) :
    decode (tag message) (encode message ++ rest) = some (message, rest) := by
  cases message <;> simp [decode, encode, tag]

end PacketPayload

/-- Tcp Packet -/
structure TcpPacket where
  packetPayload : PacketPayload
  deriving DecidableEq, Repr

namespace TcpPacket

def encodeBody (message : TcpPacket) : List UInt8 :=
  encodeUInt 1 (PacketPayload.tag message.packetPayload)
    ++ (PacketPayload.encode message.packetPayload)

def decodeBody (bytes : List UInt8) : Option (TcpPacket × List UInt8) := do
  let (packetType, bytes) ← decodeUInt 1 bytes
  let (packetPayload, bytes) ← PacketPayload.decode packetType bytes
  pure ({ packetPayload }, bytes)

theorem decodeBody_encodeBody (message : TcpPacket) (rest : List UInt8) :
    decodeBody (encodeBody message ++ rest) = some (message, rest) := by
  unfold decodeBody encodeBody
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [PacketPayload.decode_encode, some_bind]
  rfl

/-- Every body fits the length prefix -/
theorem encodeBody_length_lt (message : TcpPacket) : (encodeBody message).length + 2 < 256 ^ 2 := by
  unfold encodeBody
  cases message.packetPayload with
  | loginMessage inner =>
    simp only [PacketPayload.encode, List.length_append, encodeUInt_length, LoginMessage.encode_length]
    omega
  | clientHeartbeatMessage inner =>
    simp only [PacketPayload.encode, List.length_append, encodeUInt_length, ClientHeartbeatMessage.encode_length]
    omega
  | successfulLoginMessage inner =>
    simp only [PacketPayload.encode, List.length_append, encodeUInt_length, SuccessfulLoginMessage.encode_length]
    omega
  | loginRejectMessage inner =>
    simp only [PacketPayload.encode, List.length_append, encodeUInt_length, LoginRejectMessage.encode_length]
    omega
  | serverHeartbeatMessage inner =>
    simp only [PacketPayload.encode, List.length_append, encodeUInt_length, ServerHeartbeatMessage.encode_length]
    omega
  | binaryDataMessage inner =>
    have bound_inner := BinaryDataMessage.encode_length_le inner
    simp only [PacketPayload.encode, List.length_append, encodeUInt_length]
    omega

/-- Size rule: Length counts the bytes after it plus 2, so it is written from the body and checked on decode -/
def encode : TcpPacket → List UInt8 :=
  encodeFramedLE 2 2 encodeBody

def decode : List UInt8 → Option (TcpPacket × List UInt8) :=
  decodeFramedLE 2 2 decodeBody

@[simp] theorem decode_encode (message : TcpPacket) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) :=
  decodeFramedLE_encodeFramedLE 2 2 encodeBody decodeBody message (decodeBody_encodeBody message) (encodeBody_length_lt message) rest

theorem encode_length_pos (message : TcpPacket) : (encode message).length > 0 := by
  unfold encode
  rw [encodeFramedLE_length]
  omega

end TcpPacket

/-- Packet -/
structure Packet where
  tcpPacket : List TcpPacket
  deriving DecidableEq, Repr

namespace Packet

def encode (message : Packet) : List UInt8 :=
  encodeMany TcpPacket.encode message.tcpPacket

def decode (bytes : List UInt8) : Option Packet := do
  let tcpPacket ← decodeAll TcpPacket.decode bytes.length bytes
  pure { tcpPacket }

theorem decode_encode (message : Packet) : decode (encode message) = some message := by
  unfold decode encode
  rw [decodeAll_encodeMany TcpPacket.encode TcpPacket.decode TcpPacket.decode_encode TcpPacket.encode_length_pos message.tcpPacket _ (encodeMany_length_ge TcpPacket.encode TcpPacket.encode_length_pos message.tcpPacket), some_bind]
  rfl

end Packet

end Omi.CixatsCixaspenSnapshotTcpoutV11
