import Omi.Wire

/-!
# Blue Ocean Technologies Member Order Information Record Depth Feed v1.3

Generated from the binary model, with the proofs the model's rules call for: every record
decodes back to what was encoded; a message dispatch selects the message its type names;
a count is written from the list it counts; a length prefix is written from the bytes it frames;
and a packet read to the end of its data decodes to the messages that were written.

Note: Sbe Message is not framed: its size rule is not the length plus a constant the frame proof covers.

Note: Message's Message Length is written from its body but not checked on decode, since the body has no bound the prefix must fit; the body is read by its content.

Text fields are kept byte for byte, padding included, so what is decoded encodes back unchanged.
Prices with implied decimals are proven as the integers on the wire.
-/

namespace Omi.BlueoceanatsBlueequitiesMemoirdepthfeedSbeV13

/-- Security Trading Status: one byte code -/
def SecurityTradingStatus.codes : List UInt8 :=
  [0x48, 0x50, 0x51, 0x54]

inductive SecurityTradingStatus where
  | halted -- Halted
  | paused -- Paused
  | quoting -- Quoting
  | trading -- Trading
  | unlisted (byte : { byte : UInt8 // byte ∉ SecurityTradingStatus.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace SecurityTradingStatus

def toByte : SecurityTradingStatus → UInt8
  | .halted => 0x48
  | .paused => 0x50
  | .quoting => 0x51
  | .trading => 0x54
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : SecurityTradingStatus :=
  if byte = 0x48 then .halted
  else if byte = 0x50 then .paused
  else if byte = 0x51 then .quoting
  else .trading

def ofByte (byte : UInt8) : SecurityTradingStatus :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : SecurityTradingStatus) : ofByte value.toByte = value := by
  cases value with
  | halted => decide
  | paused => decide
  | quoting => decide
  | trading => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : SecurityTradingStatus) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (SecurityTradingStatus × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : SecurityTradingStatus) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : SecurityTradingStatus) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end SecurityTradingStatus

/-- Security Trading Status Reason: one byte code -/
def SecurityTradingStatusReason.codes : List UInt8 :=
  [0x58, 0x52, 0x41]

inductive SecurityTradingStatusReason where
  | none_ -- None
  | regulatory -- Regulatory
  | administrative -- Administrative
  | unlisted (byte : { byte : UInt8 // byte ∉ SecurityTradingStatusReason.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace SecurityTradingStatusReason

def toByte : SecurityTradingStatusReason → UInt8
  | .none_ => 0x58
  | .regulatory => 0x52
  | .administrative => 0x41
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : SecurityTradingStatusReason :=
  if byte = 0x58 then .none_
  else if byte = 0x52 then .regulatory
  else .administrative

def ofByte (byte : UInt8) : SecurityTradingStatusReason :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : SecurityTradingStatusReason) : ofByte value.toByte = value := by
  cases value with
  | none_ => decide
  | regulatory => decide
  | administrative => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : SecurityTradingStatusReason) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (SecurityTradingStatusReason × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : SecurityTradingStatusReason) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : SecurityTradingStatusReason) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end SecurityTradingStatusReason

/-- Trading Session: one byte code -/
def TradingSession.codes : List UInt8 :=
  [0x31, 0x32, 0x33, 0x34]

inductive TradingSession where
  | opening -- Opening
  | trading -- Trading
  | postTrading -- Post Trading
  | closed -- Closed
  | unlisted (byte : { byte : UInt8 // byte ∉ TradingSession.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace TradingSession

def toByte : TradingSession → UInt8
  | .opening => 0x31
  | .trading => 0x32
  | .postTrading => 0x33
  | .closed => 0x34
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : TradingSession :=
  if byte = 0x31 then .opening
  else if byte = 0x32 then .trading
  else if byte = 0x33 then .postTrading
  else .closed

def ofByte (byte : UInt8) : TradingSession :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : TradingSession) : ofByte value.toByte = value := by
  cases value with
  | opening => decide
  | trading => decide
  | postTrading => decide
  | closed => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : TradingSession) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (TradingSession × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : TradingSession) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : TradingSession) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end TradingSession

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

/-- Instrument Directory Message: 36 bytes -/
structure InstrumentDirectoryMessage where
  timestamp : BitVec 64
  securityId : BitVec 16
  symbol : Alpha 6
  symbolSfx : Alpha 6
  roundLot : BitVec 32
  reserved : BitVec 8
  isTestSymbol : BitVec 8
  mpv : BitVec 64
  deriving DecidableEq, Repr

namespace InstrumentDirectoryMessage

def encode (message : InstrumentDirectoryMessage) : List UInt8 :=
  encodeUInt 8 message.timestamp
    ++ (encodeUInt 2 message.securityId
    ++ (Alpha.encode message.symbol
    ++ (Alpha.encode message.symbolSfx
    ++ (encodeUInt 4 message.roundLot
    ++ (encodeUInt 1 message.reserved
    ++ (encodeUInt 1 message.isTestSymbol
    ++ (encodeUInt 8 message.mpv)))))))

def decode (bytes : List UInt8) : Option (InstrumentDirectoryMessage × List UInt8) := do
  let (timestamp, bytes) ← decodeUInt 8 bytes
  let (securityId, bytes) ← decodeUInt 2 bytes
  let (symbol, bytes) ← Alpha.decode 6 bytes
  let (symbolSfx, bytes) ← Alpha.decode 6 bytes
  let (roundLot, bytes) ← decodeUInt 4 bytes
  let (reserved, bytes) ← decodeUInt 1 bytes
  let (isTestSymbol, bytes) ← decodeUInt 1 bytes
  let (mpv, bytes) ← decodeUInt 8 bytes
  pure ({ timestamp, securityId, symbol, symbolSfx, roundLot, reserved, isTestSymbol, mpv }, bytes)

@[simp] theorem encode_length (message : InstrumentDirectoryMessage) : (encode message).length = 36 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Alpha.encode_length]

theorem encode_length_pos (message : InstrumentDirectoryMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : InstrumentDirectoryMessage) (rest : List UInt8) :
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
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end InstrumentDirectoryMessage

/-- Reg Sho Restriction Message: 11 bytes -/
structure RegShoRestrictionMessage where
  timestamp : BitVec 64
  securityId : BitVec 16
  shortSaleRestriction : BitVec 8
  deriving DecidableEq, Repr

namespace RegShoRestrictionMessage

def encode (message : RegShoRestrictionMessage) : List UInt8 :=
  encodeUInt 8 message.timestamp
    ++ (encodeUInt 2 message.securityId
    ++ (encodeUInt 1 message.shortSaleRestriction))

def decode (bytes : List UInt8) : Option (RegShoRestrictionMessage × List UInt8) := do
  let (timestamp, bytes) ← decodeUInt 8 bytes
  let (securityId, bytes) ← decodeUInt 2 bytes
  let (shortSaleRestriction, bytes) ← decodeUInt 1 bytes
  pure ({ timestamp, securityId, shortSaleRestriction }, bytes)

@[simp] theorem encode_length (message : RegShoRestrictionMessage) : (encode message).length = 11 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length]

theorem encode_length_pos (message : RegShoRestrictionMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : RegShoRestrictionMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end RegShoRestrictionMessage

/-- Security Trading Status Message: 12 bytes -/
structure SecurityTradingStatusMessage where
  timestamp : BitVec 64
  securityId : BitVec 16
  securityTradingStatus : SecurityTradingStatus
  securityTradingStatusReason : SecurityTradingStatusReason
  deriving DecidableEq, Repr

namespace SecurityTradingStatusMessage

def encode (message : SecurityTradingStatusMessage) : List UInt8 :=
  encodeUInt 8 message.timestamp
    ++ (encodeUInt 2 message.securityId
    ++ (SecurityTradingStatus.encode message.securityTradingStatus
    ++ (SecurityTradingStatusReason.encode message.securityTradingStatusReason)))

def decode (bytes : List UInt8) : Option (SecurityTradingStatusMessage × List UInt8) := do
  let (timestamp, bytes) ← decodeUInt 8 bytes
  let (securityId, bytes) ← decodeUInt 2 bytes
  let (securityTradingStatus, bytes) ← SecurityTradingStatus.decode bytes
  let (securityTradingStatusReason, bytes) ← SecurityTradingStatusReason.decode bytes
  pure ({ timestamp, securityId, securityTradingStatus, securityTradingStatusReason }, bytes)

@[simp] theorem encode_length (message : SecurityTradingStatusMessage) : (encode message).length = 12 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, SecurityTradingStatus.encode_length, SecurityTradingStatusReason.encode_length]

theorem encode_length_pos (message : SecurityTradingStatusMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SecurityTradingStatusMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, SecurityTradingStatus.decode_encode, some_bind]
  dsimp only
  rw [SecurityTradingStatusReason.decode_encode, some_bind]
  rfl

end SecurityTradingStatusMessage

/-- Trading Session Status Message: 9 bytes -/
structure TradingSessionStatusMessage where
  timestamp : BitVec 64
  tradingSession : TradingSession
  deriving DecidableEq, Repr

namespace TradingSessionStatusMessage

def encode (message : TradingSessionStatusMessage) : List UInt8 :=
  encodeUInt 8 message.timestamp
    ++ (TradingSession.encode message.tradingSession)

def decode (bytes : List UInt8) : Option (TradingSessionStatusMessage × List UInt8) := do
  let (timestamp, bytes) ← decodeUInt 8 bytes
  let (tradingSession, bytes) ← TradingSession.decode bytes
  pure ({ timestamp, tradingSession }, bytes)

@[simp] theorem encode_length (message : TradingSessionStatusMessage) : (encode message).length = 9 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, TradingSession.encode_length]

theorem encode_length_pos (message : TradingSessionStatusMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : TradingSessionStatusMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [TradingSession.decode_encode, some_bind]
  rfl

end TradingSessionStatusMessage

/-- Order Added Message: 31 bytes -/
structure OrderAddedMessage where
  timestamp : BitVec 64
  securityId : BitVec 16
  orderId : BitVec 64
  side : Side
  quantity : BitVec 32
  price : BitVec 64
  deriving DecidableEq, Repr

namespace OrderAddedMessage

def encode (message : OrderAddedMessage) : List UInt8 :=
  encodeUInt 8 message.timestamp
    ++ (encodeUInt 2 message.securityId
    ++ (encodeUInt 8 message.orderId
    ++ (Side.encode message.side
    ++ (encodeUInt 4 message.quantity
    ++ (encodeUInt 8 message.price)))))

def decode (bytes : List UInt8) : Option (OrderAddedMessage × List UInt8) := do
  let (timestamp, bytes) ← decodeUInt 8 bytes
  let (securityId, bytes) ← decodeUInt 2 bytes
  let (orderId, bytes) ← decodeUInt 8 bytes
  let (side, bytes) ← Side.decode bytes
  let (quantity, bytes) ← decodeUInt 4 bytes
  let (price, bytes) ← decodeUInt 8 bytes
  pure ({ timestamp, securityId, orderId, side, quantity, price }, bytes)

@[simp] theorem encode_length (message : OrderAddedMessage) : (encode message).length = 31 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Side.encode_length]

theorem encode_length_pos (message : OrderAddedMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OrderAddedMessage) (rest : List UInt8) :
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
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end OrderAddedMessage

/-- Order Deleted Message: 18 bytes -/
structure OrderDeletedMessage where
  timestamp : BitVec 64
  securityId : BitVec 16
  orderId : BitVec 64
  deriving DecidableEq, Repr

namespace OrderDeletedMessage

def encode (message : OrderDeletedMessage) : List UInt8 :=
  encodeUInt 8 message.timestamp
    ++ (encodeUInt 2 message.securityId
    ++ (encodeUInt 8 message.orderId))

def decode (bytes : List UInt8) : Option (OrderDeletedMessage × List UInt8) := do
  let (timestamp, bytes) ← decodeUInt 8 bytes
  let (securityId, bytes) ← decodeUInt 2 bytes
  let (orderId, bytes) ← decodeUInt 8 bytes
  pure ({ timestamp, securityId, orderId }, bytes)

@[simp] theorem encode_length (message : OrderDeletedMessage) : (encode message).length = 18 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length]

theorem encode_length_pos (message : OrderDeletedMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OrderDeletedMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end OrderDeletedMessage

/-- Order Reduced Message: 22 bytes -/
structure OrderReducedMessage where
  timestamp : BitVec 64
  securityId : BitVec 16
  orderId : BitVec 64
  quantity : BitVec 32
  deriving DecidableEq, Repr

namespace OrderReducedMessage

def encode (message : OrderReducedMessage) : List UInt8 :=
  encodeUInt 8 message.timestamp
    ++ (encodeUInt 2 message.securityId
    ++ (encodeUInt 8 message.orderId
    ++ (encodeUInt 4 message.quantity)))

def decode (bytes : List UInt8) : Option (OrderReducedMessage × List UInt8) := do
  let (timestamp, bytes) ← decodeUInt 8 bytes
  let (securityId, bytes) ← decodeUInt 2 bytes
  let (orderId, bytes) ← decodeUInt 8 bytes
  let (quantity, bytes) ← decodeUInt 4 bytes
  pure ({ timestamp, securityId, orderId, quantity }, bytes)

@[simp] theorem encode_length (message : OrderReducedMessage) : (encode message).length = 22 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length]

theorem encode_length_pos (message : OrderReducedMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OrderReducedMessage) (rest : List UInt8) :
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

end OrderReducedMessage

/-- Order Executed Message: 38 bytes -/
structure OrderExecutedMessage where
  timestamp : BitVec 64
  securityId : BitVec 16
  orderId : BitVec 64
  tradeId : BitVec 64
  quantity : BitVec 32
  price : BitVec 64
  deriving DecidableEq, Repr

namespace OrderExecutedMessage

def encode (message : OrderExecutedMessage) : List UInt8 :=
  encodeUInt 8 message.timestamp
    ++ (encodeUInt 2 message.securityId
    ++ (encodeUInt 8 message.orderId
    ++ (encodeUInt 8 message.tradeId
    ++ (encodeUInt 4 message.quantity
    ++ (encodeUInt 8 message.price)))))

def decode (bytes : List UInt8) : Option (OrderExecutedMessage × List UInt8) := do
  let (timestamp, bytes) ← decodeUInt 8 bytes
  let (securityId, bytes) ← decodeUInt 2 bytes
  let (orderId, bytes) ← decodeUInt 8 bytes
  let (tradeId, bytes) ← decodeUInt 8 bytes
  let (quantity, bytes) ← decodeUInt 4 bytes
  let (price, bytes) ← decodeUInt 8 bytes
  pure ({ timestamp, securityId, orderId, tradeId, quantity, price }, bytes)

@[simp] theorem encode_length (message : OrderExecutedMessage) : (encode message).length = 38 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length]

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
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end OrderExecutedMessage

/-- Trade Message: 30 bytes -/
structure TradeMessage where
  timestamp : BitVec 64
  securityId : BitVec 16
  tradeId : BitVec 64
  quantity : BitVec 32
  price : BitVec 64
  deriving DecidableEq, Repr

namespace TradeMessage

def encode (message : TradeMessage) : List UInt8 :=
  encodeUInt 8 message.timestamp
    ++ (encodeUInt 2 message.securityId
    ++ (encodeUInt 8 message.tradeId
    ++ (encodeUInt 4 message.quantity
    ++ (encodeUInt 8 message.price))))

def decode (bytes : List UInt8) : Option (TradeMessage × List UInt8) := do
  let (timestamp, bytes) ← decodeUInt 8 bytes
  let (securityId, bytes) ← decodeUInt 2 bytes
  let (tradeId, bytes) ← decodeUInt 8 bytes
  let (quantity, bytes) ← decodeUInt 4 bytes
  let (price, bytes) ← decodeUInt 8 bytes
  pure ({ timestamp, securityId, tradeId, quantity, price }, bytes)

@[simp] theorem encode_length (message : TradeMessage) : (encode message).length = 30 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length]

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
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end TradeMessage

/-- Broken Trade Message: 30 bytes -/
structure BrokenTradeMessage where
  timestamp : BitVec 64
  securityId : BitVec 16
  tradeId : BitVec 64
  originalQuantity : BitVec 32
  originalPrice : BitVec 64
  deriving DecidableEq, Repr

namespace BrokenTradeMessage

def encode (message : BrokenTradeMessage) : List UInt8 :=
  encodeUInt 8 message.timestamp
    ++ (encodeUInt 2 message.securityId
    ++ (encodeUInt 8 message.tradeId
    ++ (encodeUInt 4 message.originalQuantity
    ++ (encodeUInt 8 message.originalPrice))))

def decode (bytes : List UInt8) : Option (BrokenTradeMessage × List UInt8) := do
  let (timestamp, bytes) ← decodeUInt 8 bytes
  let (securityId, bytes) ← decodeUInt 2 bytes
  let (tradeId, bytes) ← decodeUInt 8 bytes
  let (originalQuantity, bytes) ← decodeUInt 4 bytes
  let (originalPrice, bytes) ← decodeUInt 8 bytes
  pure ({ timestamp, securityId, tradeId, originalQuantity, originalPrice }, bytes)

@[simp] theorem encode_length (message : BrokenTradeMessage) : (encode message).length = 30 := by
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
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end BrokenTradeMessage

/-- Corrected Trade Message: 42 bytes -/
structure CorrectedTradeMessage where
  timestamp : BitVec 64
  securityId : BitVec 16
  tradeId : BitVec 64
  originalQuantity : BitVec 32
  originalPrice : BitVec 64
  correctedQuantity : BitVec 32
  correctedPrice : BitVec 64
  deriving DecidableEq, Repr

namespace CorrectedTradeMessage

def encode (message : CorrectedTradeMessage) : List UInt8 :=
  encodeUInt 8 message.timestamp
    ++ (encodeUInt 2 message.securityId
    ++ (encodeUInt 8 message.tradeId
    ++ (encodeUInt 4 message.originalQuantity
    ++ (encodeUInt 8 message.originalPrice
    ++ (encodeUInt 4 message.correctedQuantity
    ++ (encodeUInt 8 message.correctedPrice))))))

def decode (bytes : List UInt8) : Option (CorrectedTradeMessage × List UInt8) := do
  let (timestamp, bytes) ← decodeUInt 8 bytes
  let (securityId, bytes) ← decodeUInt 2 bytes
  let (tradeId, bytes) ← decodeUInt 8 bytes
  let (originalQuantity, bytes) ← decodeUInt 4 bytes
  let (originalPrice, bytes) ← decodeUInt 8 bytes
  let (correctedQuantity, bytes) ← decodeUInt 4 bytes
  let (correctedPrice, bytes) ← decodeUInt 8 bytes
  pure ({ timestamp, securityId, tradeId, originalQuantity, originalPrice, correctedQuantity, correctedPrice }, bytes)

@[simp] theorem encode_length (message : CorrectedTradeMessage) : (encode message).length = 42 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length]

theorem encode_length_pos (message : CorrectedTradeMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : CorrectedTradeMessage) (rest : List UInt8) :
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
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end CorrectedTradeMessage

/-- Clear Book Message: 10 bytes -/
structure ClearBookMessage where
  timestamp : BitVec 64
  securityId : BitVec 16
  deriving DecidableEq, Repr

namespace ClearBookMessage

def encode (message : ClearBookMessage) : List UInt8 :=
  encodeUInt 8 message.timestamp
    ++ (encodeUInt 2 message.securityId)

def decode (bytes : List UInt8) : Option (ClearBookMessage × List UInt8) := do
  let (timestamp, bytes) ← decodeUInt 8 bytes
  let (securityId, bytes) ← decodeUInt 2 bytes
  pure ({ timestamp, securityId }, bytes)

@[simp] theorem encode_length (message : ClearBookMessage) : (encode message).length = 10 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length]

theorem encode_length_pos (message : ClearBookMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : ClearBookMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end ClearBookMessage

/-- Snapshot Complete Message: 16 bytes -/
structure SnapshotCompleteMessage where
  timestamp : BitVec 64
  asOfSequenceNumber : BitVec 64
  deriving DecidableEq, Repr

namespace SnapshotCompleteMessage

def encode (message : SnapshotCompleteMessage) : List UInt8 :=
  encodeUInt 8 message.timestamp
    ++ (encodeUInt 8 message.asOfSequenceNumber)

def decode (bytes : List UInt8) : Option (SnapshotCompleteMessage × List UInt8) := do
  let (timestamp, bytes) ← decodeUInt 8 bytes
  let (asOfSequenceNumber, bytes) ← decodeUInt 8 bytes
  pure ({ timestamp, asOfSequenceNumber }, bytes)

@[simp] theorem encode_length (message : SnapshotCompleteMessage) : (encode message).length = 16 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length]

theorem encode_length_pos (message : SnapshotCompleteMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SnapshotCompleteMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end SnapshotCompleteMessage

/-- Any Payload, selected by Template Id -/
inductive Payload where
  | instrumentDirectoryMessage (message : InstrumentDirectoryMessage) -- 1
  | regShoRestrictionMessage (message : RegShoRestrictionMessage) -- 2
  | securityTradingStatusMessage (message : SecurityTradingStatusMessage) -- 3
  | tradingSessionStatusMessage (message : TradingSessionStatusMessage) -- 5
  | orderAddedMessage (message : OrderAddedMessage) -- 10
  | orderDeletedMessage (message : OrderDeletedMessage) -- 11
  | orderReducedMessage (message : OrderReducedMessage) -- 12
  | orderExecutedMessage (message : OrderExecutedMessage) -- 13
  | tradeMessage (message : TradeMessage) -- 14
  | brokenTradeMessage (message : BrokenTradeMessage) -- 15
  | correctedTradeMessage (message : CorrectedTradeMessage) -- 16
  | clearBookMessage (message : ClearBookMessage) -- 18
  | snapshotCompleteMessage (message : SnapshotCompleteMessage) -- 100
  deriving DecidableEq, Repr

namespace Payload

/-- The Template Id each message is sent under -/
def tag : Payload → BitVec 8
  | .instrumentDirectoryMessage _ => 1
  | .regShoRestrictionMessage _ => 2
  | .securityTradingStatusMessage _ => 3
  | .tradingSessionStatusMessage _ => 5
  | .orderAddedMessage _ => 10
  | .orderDeletedMessage _ => 11
  | .orderReducedMessage _ => 12
  | .orderExecutedMessage _ => 13
  | .tradeMessage _ => 14
  | .brokenTradeMessage _ => 15
  | .correctedTradeMessage _ => 16
  | .clearBookMessage _ => 18
  | .snapshotCompleteMessage _ => 100

def encode : Payload → List UInt8
  | .instrumentDirectoryMessage message => InstrumentDirectoryMessage.encode message
  | .regShoRestrictionMessage message => RegShoRestrictionMessage.encode message
  | .securityTradingStatusMessage message => SecurityTradingStatusMessage.encode message
  | .tradingSessionStatusMessage message => TradingSessionStatusMessage.encode message
  | .orderAddedMessage message => OrderAddedMessage.encode message
  | .orderDeletedMessage message => OrderDeletedMessage.encode message
  | .orderReducedMessage message => OrderReducedMessage.encode message
  | .orderExecutedMessage message => OrderExecutedMessage.encode message
  | .tradeMessage message => TradeMessage.encode message
  | .brokenTradeMessage message => BrokenTradeMessage.encode message
  | .correctedTradeMessage message => CorrectedTradeMessage.encode message
  | .clearBookMessage message => ClearBookMessage.encode message
  | .snapshotCompleteMessage message => SnapshotCompleteMessage.encode message

/-- The most bytes any message's encoding can take -/
theorem encode_length_le (message : Payload) : (encode message).length ≤ 42 := by
  cases message with
  | instrumentDirectoryMessage inner =>
    simp only [encode, InstrumentDirectoryMessage.encode_length]
    omega
  | regShoRestrictionMessage inner =>
    simp only [encode, RegShoRestrictionMessage.encode_length]
    omega
  | securityTradingStatusMessage inner =>
    simp only [encode, SecurityTradingStatusMessage.encode_length]
    omega
  | tradingSessionStatusMessage inner =>
    simp only [encode, TradingSessionStatusMessage.encode_length]
    omega
  | orderAddedMessage inner =>
    simp only [encode, OrderAddedMessage.encode_length]
    omega
  | orderDeletedMessage inner =>
    simp only [encode, OrderDeletedMessage.encode_length]
    omega
  | orderReducedMessage inner =>
    simp only [encode, OrderReducedMessage.encode_length]
    omega
  | orderExecutedMessage inner =>
    simp only [encode, OrderExecutedMessage.encode_length]
    omega
  | tradeMessage inner =>
    simp only [encode, TradeMessage.encode_length]
    omega
  | brokenTradeMessage inner =>
    simp only [encode, BrokenTradeMessage.encode_length]
    omega
  | correctedTradeMessage inner =>
    simp only [encode, CorrectedTradeMessage.encode_length]
    omega
  | clearBookMessage inner =>
    simp only [encode, ClearBookMessage.encode_length]
    omega
  | snapshotCompleteMessage inner =>
    simp only [encode, SnapshotCompleteMessage.encode_length]
    omega

def decode (tag : BitVec 8) (bytes : List UInt8) : Option (Payload × List UInt8) :=
  if tag = 1 then (InstrumentDirectoryMessage.decode bytes).map fun (message, rest) => (.instrumentDirectoryMessage message, rest)
  else if tag = 2 then (RegShoRestrictionMessage.decode bytes).map fun (message, rest) => (.regShoRestrictionMessage message, rest)
  else if tag = 3 then (SecurityTradingStatusMessage.decode bytes).map fun (message, rest) => (.securityTradingStatusMessage message, rest)
  else if tag = 5 then (TradingSessionStatusMessage.decode bytes).map fun (message, rest) => (.tradingSessionStatusMessage message, rest)
  else if tag = 10 then (OrderAddedMessage.decode bytes).map fun (message, rest) => (.orderAddedMessage message, rest)
  else if tag = 11 then (OrderDeletedMessage.decode bytes).map fun (message, rest) => (.orderDeletedMessage message, rest)
  else if tag = 12 then (OrderReducedMessage.decode bytes).map fun (message, rest) => (.orderReducedMessage message, rest)
  else if tag = 13 then (OrderExecutedMessage.decode bytes).map fun (message, rest) => (.orderExecutedMessage message, rest)
  else if tag = 14 then (TradeMessage.decode bytes).map fun (message, rest) => (.tradeMessage message, rest)
  else if tag = 15 then (BrokenTradeMessage.decode bytes).map fun (message, rest) => (.brokenTradeMessage message, rest)
  else if tag = 16 then (CorrectedTradeMessage.decode bytes).map fun (message, rest) => (.correctedTradeMessage message, rest)
  else if tag = 18 then (ClearBookMessage.decode bytes).map fun (message, rest) => (.clearBookMessage message, rest)
  else if tag = 100 then (SnapshotCompleteMessage.decode bytes).map fun (message, rest) => (.snapshotCompleteMessage message, rest)
  else none

@[simp] theorem decode_encode (message : Payload) (rest : List UInt8) :
    decode (tag message) (encode message ++ rest) = some (message, rest) := by
  cases message <;> simp [decode, encode, tag]

end Payload

/-- Sbe Message -/
structure SbeMessage where
  blockLength : BitVec 16
  schemaId : BitVec 8
  version : BitVec 16
  payload : Payload
  deriving DecidableEq, Repr

namespace SbeMessage

def encode (message : SbeMessage) : List UInt8 :=
  encodeUInt 2 message.blockLength
    ++ (encodeUInt 1 (Payload.tag message.payload)
    ++ (encodeUInt 1 message.schemaId
    ++ (encodeUInt 2 message.version
    ++ (Payload.encode message.payload))))

def decode (bytes : List UInt8) : Option (SbeMessage × List UInt8) := do
  let (blockLength, bytes) ← decodeUInt 2 bytes
  let (templateId, bytes) ← decodeUInt 1 bytes
  let (schemaId, bytes) ← decodeUInt 1 bytes
  let (version, bytes) ← decodeUInt 2 bytes
  let (payload, bytes) ← Payload.decode templateId bytes
  pure ({ blockLength, schemaId, version, payload }, bytes)

theorem encode_length_pos (message : SbeMessage) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUInt_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : SbeMessage) : (encode message).length ≤ 48 := by
  unfold encode
  cases message.payload with
  | instrumentDirectoryMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, InstrumentDirectoryMessage.encode_length]
    omega
  | regShoRestrictionMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, RegShoRestrictionMessage.encode_length]
    omega
  | securityTradingStatusMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, SecurityTradingStatusMessage.encode_length]
    omega
  | tradingSessionStatusMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, TradingSessionStatusMessage.encode_length]
    omega
  | orderAddedMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, OrderAddedMessage.encode_length]
    omega
  | orderDeletedMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, OrderDeletedMessage.encode_length]
    omega
  | orderReducedMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, OrderReducedMessage.encode_length]
    omega
  | orderExecutedMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, OrderExecutedMessage.encode_length]
    omega
  | tradeMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, TradeMessage.encode_length]
    omega
  | brokenTradeMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, BrokenTradeMessage.encode_length]
    omega
  | correctedTradeMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, CorrectedTradeMessage.encode_length]
    omega
  | clearBookMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, ClearBookMessage.encode_length]
    omega
  | snapshotCompleteMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, SnapshotCompleteMessage.encode_length]
    omega

@[simp] theorem decode_encode (message : SbeMessage) (rest : List UInt8) :
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
  rw [Payload.decode_encode, some_bind]
  rfl

end SbeMessage

/-- Message -/
structure Message where
  sbeMessage : SbeMessage
  deriving DecidableEq, Repr

namespace Message

def encodeBody (message : Message) : List UInt8 :=
  SbeMessage.encode message.sbeMessage

def decodeBody (bytes : List UInt8) : Option (Message × List UInt8) := do
  let (sbeMessage, bytes) ← SbeMessage.decode bytes
  pure ({ sbeMessage }, bytes)

theorem decodeBody_encodeBody (message : Message) (rest : List UInt8) :
    decodeBody (encodeBody message ++ rest) = some (message, rest) := by
  unfold decodeBody encodeBody
  rw [SbeMessage.decode_encode, some_bind]
  rfl

/-- Size rule: Message Length counts the bytes after it, so it is written from the body; the body has no bound the prefix must fit, so it is read by its content and the prefix is not checked -/
def encode (message : Message) : List UInt8 :=
  encodeUInt 2 (BitVec.ofNat (8 * 2) ((encodeBody message).length + 0)) ++ encodeBody message

def decode (bytes : List UInt8) : Option (Message × List UInt8) := do
  let (_, bytes) ← decodeUInt 2 bytes
  decodeBody bytes

@[simp] theorem decode_encode (message : Message) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  exact decodeBody_encodeBody message rest

theorem encode_length_pos (message : Message) : (encode message).length > 0 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length]
  omega

end Message

/-- Sequenced Message -/
structure SequencedMessage where
  message : Bounded 2 Message
  deriving DecidableEq, Repr

namespace SequencedMessage

def encode (message : SequencedMessage) : List UInt8 :=
  encodeUInt 2 (BitVec.ofNat (8 * 2) message.message.val.length)
    ++ (encodeMany Message.encode message.message.val)

def decode (bytes : List UInt8) : Option (SequencedMessage × List UInt8) := do
  let (messageCount, bytes) ← decodeUInt 2 bytes
  let (message_, bytes) ← decodeMany Message.decode messageCount.toNat bytes
  if fits_message : message_.length < 256 ^ 2 then
    pure ({ message := ⟨message_, fits_message⟩ }, bytes)
  else none

theorem encode_length_pos (message : SequencedMessage) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUInt_length, List.length_append]
  omega

@[simp] theorem decode_encode (message : SequencedMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeMany_bounded 2 Message.encode Message.decode Message.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.message.length_lt]
  rfl

end SequencedMessage

/-- Any Sequenced Messages, selected by Message Type -/
inductive SequencedMessages where
  | sequencedMessage (message : SequencedMessage) -- 2
  deriving DecidableEq, Repr

namespace SequencedMessages

/-- The Message Type each message is sent under -/
def tag : SequencedMessages → BitVec 8
  | .sequencedMessage _ => 2

def encode : SequencedMessages → List UInt8
  | .sequencedMessage message => SequencedMessage.encode message

def decode (tag : BitVec 8) (bytes : List UInt8) : Option (SequencedMessages × List UInt8) :=
  if tag = 2 then (SequencedMessage.decode bytes).map fun (message, rest) => (.sequencedMessage message, rest)
  else none

@[simp] theorem decode_encode (message : SequencedMessages) (rest : List UInt8) :
    decode (tag message) (encode message ++ rest) = some (message, rest) := by
  cases message <;> simp [decode, encode, tag]

end SequencedMessages

/-- Packet -/
structure Packet where
  headerLength : BitVec 8
  sessionId : BitVec 64
  sequenceNumber : BitVec 64
  sequencedMessages : SequencedMessages
  deriving DecidableEq, Repr

namespace Packet

def encode (message : Packet) : List UInt8 :=
  encodeUInt 1 (SequencedMessages.tag message.sequencedMessages)
    ++ (encodeUInt 1 message.headerLength
    ++ (encodeUInt 8 message.sessionId
    ++ (encodeUInt 8 message.sequenceNumber
    ++ (SequencedMessages.encode message.sequencedMessages))))

def decode (bytes : List UInt8) : Option (Packet × List UInt8) := do
  let (messageType, bytes) ← decodeUInt 1 bytes
  let (headerLength, bytes) ← decodeUInt 1 bytes
  let (sessionId, bytes) ← decodeUInt 8 bytes
  let (sequenceNumber, bytes) ← decodeUInt 8 bytes
  let (sequencedMessages, bytes) ← SequencedMessages.decode messageType bytes
  pure ({ headerLength, sessionId, sequenceNumber, sequencedMessages }, bytes)

theorem encode_length_pos (message : Packet) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUInt_length, List.length_append, ← Nat.add_assoc]
  omega

@[simp] theorem decode_encode (message : Packet) (rest : List UInt8) :
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
  rw [SequencedMessages.decode_encode, some_bind]
  rfl

end Packet

end Omi.BlueoceanatsBlueequitiesMemoirdepthfeedSbeV13
