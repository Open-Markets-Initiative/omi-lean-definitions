import Omi.Wire

/-!
# CIX Trading Inc. CIX Market Data Feed v1.4

Generated from the binary model, with the proofs the model's rules call for: every record
decodes back to what was encoded; a message dispatch selects the message its type names;
a count is written from the list it counts; a length prefix is written from the bytes it frames;
and a packet read to the end of its data decodes to the messages that were written.

Text fields are kept byte for byte, padding included, so what is decoded encodes back unchanged.
Prices with implied decimals are proven as the integers on the wire.
-/

namespace Omi.CixatsCixaspenMarketdatafeedAspenV14

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

/-- Trade Message: 60 bytes -/
structure TradeMessage where
  symbolId : BitVec 16
  timestamp : BitVec 64
  reserved8 : BitVec 64
  side : Side
  shares : BitVec 64
  symbol : Alpha 11
  price : BitVec 64
  executionId : BitVec 64
  broker : Alpha 3
  contraBroker : Alpha 3
  deriving DecidableEq, Repr

namespace TradeMessage

def encode (message : TradeMessage) : List UInt8 :=
  encodeUIntLE 2 message.symbolId
    ++ (encodeUIntLE 8 message.timestamp
    ++ (encodeUIntLE 8 message.reserved8
    ++ (Side.encode message.side
    ++ (encodeUIntLE 8 message.shares
    ++ (Alpha.encode message.symbol
    ++ (encodeUIntLE 8 message.price
    ++ (encodeUIntLE 8 message.executionId
    ++ (Alpha.encode message.broker
    ++ (Alpha.encode message.contraBroker)))))))))

def decode (bytes : List UInt8) : Option (TradeMessage × List UInt8) := do
  let (symbolId, bytes) ← decodeUIntLE 2 bytes
  let (timestamp, bytes) ← decodeUIntLE 8 bytes
  let (reserved8, bytes) ← decodeUIntLE 8 bytes
  let (side, bytes) ← Side.decode bytes
  let (shares, bytes) ← decodeUIntLE 8 bytes
  let (symbol, bytes) ← Alpha.decode 11 bytes
  let (price, bytes) ← decodeUIntLE 8 bytes
  let (executionId, bytes) ← decodeUIntLE 8 bytes
  let (broker, bytes) ← Alpha.decode 3 bytes
  let (contraBroker, bytes) ← Alpha.decode 3 bytes
  pure ({ symbolId, timestamp, reserved8, side, shares, symbol, price, executionId, broker, contraBroker }, bytes)

@[simp] theorem encode_length (message : TradeMessage) : (encode message).length = 60 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Side.encode_length, Alpha.encode_length]

theorem encode_length_pos (message : TradeMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : TradeMessage) (rest : List UInt8) :
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
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end TradeMessage

/-- Trade Cancel Message: 60 bytes -/
structure TradeCancelMessage where
  symbolId : BitVec 16
  timestamp : BitVec 64
  reserved8 : BitVec 64
  reserved1 : Alpha 1
  shares : BitVec 64
  symbol : Alpha 11
  price : BitVec 64
  executionId : BitVec 64
  broker : Alpha 3
  contraBroker : Alpha 3
  deriving DecidableEq, Repr

namespace TradeCancelMessage

def encode (message : TradeCancelMessage) : List UInt8 :=
  encodeUIntLE 2 message.symbolId
    ++ (encodeUIntLE 8 message.timestamp
    ++ (encodeUIntLE 8 message.reserved8
    ++ (Alpha.encode message.reserved1
    ++ (encodeUIntLE 8 message.shares
    ++ (Alpha.encode message.symbol
    ++ (encodeUIntLE 8 message.price
    ++ (encodeUIntLE 8 message.executionId
    ++ (Alpha.encode message.broker
    ++ (Alpha.encode message.contraBroker)))))))))

def decode (bytes : List UInt8) : Option (TradeCancelMessage × List UInt8) := do
  let (symbolId, bytes) ← decodeUIntLE 2 bytes
  let (timestamp, bytes) ← decodeUIntLE 8 bytes
  let (reserved8, bytes) ← decodeUIntLE 8 bytes
  let (reserved1, bytes) ← Alpha.decode 1 bytes
  let (shares, bytes) ← decodeUIntLE 8 bytes
  let (symbol, bytes) ← Alpha.decode 11 bytes
  let (price, bytes) ← decodeUIntLE 8 bytes
  let (executionId, bytes) ← decodeUIntLE 8 bytes
  let (broker, bytes) ← Alpha.decode 3 bytes
  let (contraBroker, bytes) ← Alpha.decode 3 bytes
  pure ({ symbolId, timestamp, reserved8, reserved1, shares, symbol, price, executionId, broker, contraBroker }, bytes)

@[simp] theorem encode_length (message : TradeCancelMessage) : (encode message).length = 60 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length]

theorem encode_length_pos (message : TradeCancelMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : TradeCancelMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end TradeCancelMessage

/-- Trade Correct Message: 84 bytes -/
structure TradeCorrectMessage where
  symbolId : BitVec 16
  timestamp : BitVec 64
  reserved8 : BitVec 64
  reserved1 : Alpha 1
  symbol : Alpha 11
  executionId : BitVec 64
  broker : Alpha 3
  contraBroker : Alpha 3
  originalExecutionId : BitVec 64
  originalTradePrice : BitVec 64
  originalTradeQuantity : BitVec 64
  correctedTradePrice : BitVec 64
  correctedTradeQuantity : BitVec 64
  deriving DecidableEq, Repr

namespace TradeCorrectMessage

def encode (message : TradeCorrectMessage) : List UInt8 :=
  encodeUIntLE 2 message.symbolId
    ++ (encodeUIntLE 8 message.timestamp
    ++ (encodeUIntLE 8 message.reserved8
    ++ (Alpha.encode message.reserved1
    ++ (Alpha.encode message.symbol
    ++ (encodeUIntLE 8 message.executionId
    ++ (Alpha.encode message.broker
    ++ (Alpha.encode message.contraBroker
    ++ (encodeUIntLE 8 message.originalExecutionId
    ++ (encodeUIntLE 8 message.originalTradePrice
    ++ (encodeUIntLE 8 message.originalTradeQuantity
    ++ (encodeUIntLE 8 message.correctedTradePrice
    ++ (encodeUIntLE 8 message.correctedTradeQuantity))))))))))))

def decode (bytes : List UInt8) : Option (TradeCorrectMessage × List UInt8) := do
  let (symbolId, bytes) ← decodeUIntLE 2 bytes
  let (timestamp, bytes) ← decodeUIntLE 8 bytes
  let (reserved8, bytes) ← decodeUIntLE 8 bytes
  let (reserved1, bytes) ← Alpha.decode 1 bytes
  let (symbol, bytes) ← Alpha.decode 11 bytes
  let (executionId, bytes) ← decodeUIntLE 8 bytes
  let (broker, bytes) ← Alpha.decode 3 bytes
  let (contraBroker, bytes) ← Alpha.decode 3 bytes
  let (originalExecutionId, bytes) ← decodeUIntLE 8 bytes
  let (originalTradePrice, bytes) ← decodeUIntLE 8 bytes
  let (originalTradeQuantity, bytes) ← decodeUIntLE 8 bytes
  let (correctedTradePrice, bytes) ← decodeUIntLE 8 bytes
  let (correctedTradeQuantity, bytes) ← decodeUIntLE 8 bytes
  pure ({ symbolId, timestamp, reserved8, reserved1, symbol, executionId, broker, contraBroker, originalExecutionId, originalTradePrice, originalTradeQuantity, correctedTradePrice, correctedTradeQuantity }, bytes)

@[simp] theorem encode_length (message : TradeCorrectMessage) : (encode message).length = 84 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length]

theorem encode_length_pos (message : TradeCorrectMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : TradeCorrectMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end TradeCorrectMessage

/-- Any Payload, selected by Message Type -/
inductive Payload where
  | marketEventMessage (message : MarketEventMessage) -- 'A' 0x41
  | symbolInformationMessage (message : SymbolInformationMessage) -- 'B' 0x42
  | symbolStateMessage (message : SymbolStateMessage) -- 'C' 0x43
  | newOrderAddMessage (message : NewOrderAddMessage) -- 'D' 0x44
  | orderPartialCancelMessage (message : OrderPartialCancelMessage) -- 'F' 0x46
  | orderCancelAllMessage (message : OrderCancelAllMessage) -- 'G' 0x47
  | orderExecutedMessage (message : OrderExecutedMessage) -- 'J' 0x4A
  | tradeMessage (message : TradeMessage) -- 'K' 0x4B
  | tradeCancelMessage (message : TradeCancelMessage) -- 'L' 0x4C
  | tradeCorrectMessage (message : TradeCorrectMessage) -- 'M' 0x4D
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
  | .tradeMessage _ => 75
  | .tradeCancelMessage _ => 76
  | .tradeCorrectMessage _ => 77

def encode : Payload → List UInt8
  | .marketEventMessage message => MarketEventMessage.encode message
  | .symbolInformationMessage message => SymbolInformationMessage.encode message
  | .symbolStateMessage message => SymbolStateMessage.encode message
  | .newOrderAddMessage message => NewOrderAddMessage.encode message
  | .orderPartialCancelMessage message => OrderPartialCancelMessage.encode message
  | .orderCancelAllMessage message => OrderCancelAllMessage.encode message
  | .orderExecutedMessage message => OrderExecutedMessage.encode message
  | .tradeMessage message => TradeMessage.encode message
  | .tradeCancelMessage message => TradeCancelMessage.encode message
  | .tradeCorrectMessage message => TradeCorrectMessage.encode message

def decode (tag : BitVec 8) (bytes : List UInt8) : Option (Payload × List UInt8) :=
  if tag = 65 then (MarketEventMessage.decode bytes).map fun (message, rest) => (.marketEventMessage message, rest)
  else if tag = 66 then (SymbolInformationMessage.decode bytes).map fun (message, rest) => (.symbolInformationMessage message, rest)
  else if tag = 67 then (SymbolStateMessage.decode bytes).map fun (message, rest) => (.symbolStateMessage message, rest)
  else if tag = 68 then (NewOrderAddMessage.decode bytes).map fun (message, rest) => (.newOrderAddMessage message, rest)
  else if tag = 70 then (OrderPartialCancelMessage.decode bytes).map fun (message, rest) => (.orderPartialCancelMessage message, rest)
  else if tag = 71 then (OrderCancelAllMessage.decode bytes).map fun (message, rest) => (.orderCancelAllMessage message, rest)
  else if tag = 74 then (OrderExecutedMessage.decode bytes).map fun (message, rest) => (.orderExecutedMessage message, rest)
  else if tag = 75 then (TradeMessage.decode bytes).map fun (message, rest) => (.tradeMessage message, rest)
  else if tag = 76 then (TradeCancelMessage.decode bytes).map fun (message, rest) => (.tradeCancelMessage message, rest)
  else if tag = 77 then (TradeCorrectMessage.decode bytes).map fun (message, rest) => (.tradeCorrectMessage message, rest)
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
  | tradeMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, TradeMessage.encode_length]
    omega
  | tradeCancelMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, TradeCancelMessage.encode_length]
    omega
  | tradeCorrectMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, TradeCorrectMessage.encode_length]
    omega

/-- Size rule: Length counts the bytes after it, so it is written from the body and checked on decode -/
def encode : Message → List UInt8 :=
  encodeFramedLE 2 0 encodeBody

def decode : List UInt8 → Option (Message × List UInt8) :=
  decodeFramedLE 2 0 decodeBody

@[simp] theorem decode_encode (message : Message) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) :=
  decodeFramedLE_encodeFramedLE 2 0 encodeBody decodeBody message (decodeBody_encodeBody message) (encodeBody_length_lt message) rest

theorem encode_length_pos (message : Message) : (encode message).length > 0 := by
  unfold encode
  rw [encodeFramedLE_length]
  omega

end Message

/-- Packet -/
structure Packet where
  marketDayIdentifier : Alpha 9
  feedIdentifier : FeedIdentifier
  sequence : BitVec 64
  message : Bounded 2 Message
  deriving DecidableEq, Repr

namespace Packet

def encode (message : Packet) : List UInt8 :=
  Alpha.encode message.marketDayIdentifier
    ++ (FeedIdentifier.encode message.feedIdentifier
    ++ (encodeUIntLE 8 message.sequence
    ++ (encodeUIntLE 2 (BitVec.ofNat (8 * 2) message.message.val.length)
    ++ (encodeMany Message.encode message.message.val))))

def decode (bytes : List UInt8) : Option (Packet × List UInt8) := do
  let (marketDayIdentifier, bytes) ← Alpha.decode 9 bytes
  let (feedIdentifier, bytes) ← FeedIdentifier.decode bytes
  let (sequence, bytes) ← decodeUIntLE 8 bytes
  let (count, bytes) ← decodeUIntLE 2 bytes
  let (message_, bytes) ← decodeMany Message.decode count.toNat bytes
  if fits_message : message_.length < 256 ^ 2 then
    pure ({ marketDayIdentifier, feedIdentifier, sequence, message := ⟨message_, fits_message⟩ }, bytes)
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
  rw [List.append_assoc, FeedIdentifier.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeMany_bounded 2 Message.encode Message.decode Message.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.message.length_lt]
  rfl

end Packet

end Omi.CixatsCixaspenMarketdatafeedAspenV14
