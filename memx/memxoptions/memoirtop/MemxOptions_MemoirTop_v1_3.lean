import Wire

/-!
# The Members Exchange Member Order Information Record Top v1.3

Generated from the binary model, with the proofs the model's rules call for: every record
decodes back to what was encoded; a message dispatch selects the message its type names;
a count is written from the list it counts; a length prefix is written from the bytes it frames;
and a packet read to the end of its data decodes to the messages that were written.

Text fields are kept byte for byte, padding included, so what is decoded encodes back unchanged.
Prices with implied decimals are proven as the integers on the wire.
-/

namespace Omi.MemxMemxoptionsMemoirtopSbeV13

/-- Instrument Trading Status: one byte code -/
def InstrumentTradingStatus.codes : List UInt8 :=
  [0x48, 0x54]

inductive InstrumentTradingStatus where
  | halted -- Halted
  | trading -- Trading
  | unlisted (byte : { byte : UInt8 // byte ∉ InstrumentTradingStatus.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace InstrumentTradingStatus

def toByte : InstrumentTradingStatus → UInt8
  | .halted => 0x48
  | .trading => 0x54
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : InstrumentTradingStatus :=
  if byte = 0x48 then .halted
  else .trading

def ofByte (byte : UInt8) : InstrumentTradingStatus :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : InstrumentTradingStatus) : ofByte value.toByte = value := by
  cases value with
  | halted => decide
  | trading => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : InstrumentTradingStatus) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (InstrumentTradingStatus × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : InstrumentTradingStatus) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : InstrumentTradingStatus) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end InstrumentTradingStatus

/-- Instrument Trading Status Reason: one byte code -/
def InstrumentTradingStatusReason.codes : List UInt8 :=
  [0x58, 0x41]

inductive InstrumentTradingStatusReason where
  | none_ -- None
  | administrative -- Administrative
  | unlisted (byte : { byte : UInt8 // byte ∉ InstrumentTradingStatusReason.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace InstrumentTradingStatusReason

def toByte : InstrumentTradingStatusReason → UInt8
  | .none_ => 0x58
  | .administrative => 0x41
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : InstrumentTradingStatusReason :=
  if byte = 0x58 then .none_
  else .administrative

def ofByte (byte : UInt8) : InstrumentTradingStatusReason :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : InstrumentTradingStatusReason) : ofByte value.toByte = value := by
  cases value with
  | none_ => decide
  | administrative => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : InstrumentTradingStatusReason) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (InstrumentTradingStatusReason × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : InstrumentTradingStatusReason) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : InstrumentTradingStatusReason) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end InstrumentTradingStatusReason

/-- Trading Session: one byte code -/
def TradingSession.codes : List UInt8 :=
  [0x31, 0x32]

inductive TradingSession where
  | trading -- Trading
  | closed -- Closed
  | unlisted (byte : { byte : UInt8 // byte ∉ TradingSession.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace TradingSession

def toByte : TradingSession → UInt8
  | .trading => 0x31
  | .closed => 0x32
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : TradingSession :=
  if byte = 0x31 then .trading
  else .closed

def ofByte (byte : UInt8) : TradingSession :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : TradingSession) : ofByte value.toByte = value := by
  cases value with
  | trading => decide
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

/-- Capacity: one byte code -/
def Capacity.codes : List UInt8 :=
  [0x43, 0x4E]

inductive Capacity where
  | customer -- Customer
  | nonCustomer -- Non Customer
  | unlisted (byte : { byte : UInt8 // byte ∉ Capacity.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace Capacity

def toByte : Capacity → UInt8
  | .customer => 0x43
  | .nonCustomer => 0x4E
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : Capacity :=
  if byte = 0x43 then .customer
  else .nonCustomer

def ofByte (byte : UInt8) : Capacity :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : Capacity) : ofByte value.toByte = value := by
  cases value with
  | customer => decide
  | nonCustomer => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : Capacity) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (Capacity × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : Capacity) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : Capacity) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end Capacity

/-- Heartbeat: 0 bytes -/
structure Heartbeat where
  deriving DecidableEq, Repr

namespace Heartbeat

def encode (_ : Heartbeat) : List UInt8 :=
  []

def decode (bytes : List UInt8) : Option (Heartbeat × List UInt8) :=
  some (⟨⟩, bytes)

@[simp] theorem encode_length (message : Heartbeat) : (encode message).length = 0 := by
  simp [encode]

@[simp] theorem decode_encode (message : Heartbeat) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  simp [decode, encode]

end Heartbeat

/-- Session Shutdown: 0 bytes -/
structure SessionShutdown where
  deriving DecidableEq, Repr

namespace SessionShutdown

def encode (_ : SessionShutdown) : List UInt8 :=
  []

def decode (bytes : List UInt8) : Option (SessionShutdown × List UInt8) :=
  some (⟨⟩, bytes)

@[simp] theorem encode_length (message : SessionShutdown) : (encode message).length = 0 := by
  simp [encode]

@[simp] theorem decode_encode (message : SessionShutdown) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  simp [decode, encode]

end SessionShutdown

/-- Instrument Directory Message: 56 bytes -/
structure InstrumentDirectoryMessage where
  timestamp : BitVec 64
  symbol : Alpha 8
  optionsProductType : BitVec 8
  underlier : Alpha 6
  osiRoot : Alpha 6
  maturityDate : Alpha 8
  strikePutOrCall : BitVec 8
  strikePrice : BitVec 64
  closingOnly : BitVec 8
  closingTime : BitVec 64
  isTestSymbol : BitVec 8
  deriving DecidableEq, Repr

namespace InstrumentDirectoryMessage

def encode (message : InstrumentDirectoryMessage) : List UInt8 :=
  encodeUInt 8 message.timestamp
    ++ (Alpha.encode message.symbol
    ++ (encodeUInt 1 message.optionsProductType
    ++ (Alpha.encode message.underlier
    ++ (Alpha.encode message.osiRoot
    ++ (Alpha.encode message.maturityDate
    ++ (encodeUInt 1 message.strikePutOrCall
    ++ (encodeUInt 8 message.strikePrice
    ++ (encodeUInt 1 message.closingOnly
    ++ (encodeUInt 8 message.closingTime
    ++ (encodeUInt 1 message.isTestSymbol))))))))))

def decode (bytes : List UInt8) : Option (InstrumentDirectoryMessage × List UInt8) := do
  let (timestamp, bytes) ← decodeUInt 8 bytes
  let (symbol, bytes) ← Alpha.decode 8 bytes
  let (optionsProductType, bytes) ← decodeUInt 1 bytes
  let (underlier, bytes) ← Alpha.decode 6 bytes
  let (osiRoot, bytes) ← Alpha.decode 6 bytes
  let (maturityDate, bytes) ← Alpha.decode 8 bytes
  let (strikePutOrCall, bytes) ← decodeUInt 1 bytes
  let (strikePrice, bytes) ← decodeUInt 8 bytes
  let (closingOnly, bytes) ← decodeUInt 1 bytes
  let (closingTime, bytes) ← decodeUInt 8 bytes
  let (isTestSymbol, bytes) ← decodeUInt 1 bytes
  pure ({ timestamp, symbol, optionsProductType, underlier, osiRoot, maturityDate, strikePutOrCall, strikePrice, closingOnly, closingTime, isTestSymbol }, bytes)

@[simp] theorem encode_length (message : InstrumentDirectoryMessage) : (encode message).length = 56 := by
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
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
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
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end InstrumentDirectoryMessage

/-- Instrument Trading Status Message: 18 bytes -/
structure InstrumentTradingStatusMessage where
  timestamp : BitVec 64
  symbol : Alpha 8
  instrumentTradingStatus : InstrumentTradingStatus
  instrumentTradingStatusReason : InstrumentTradingStatusReason
  deriving DecidableEq, Repr

namespace InstrumentTradingStatusMessage

def encode (message : InstrumentTradingStatusMessage) : List UInt8 :=
  encodeUInt 8 message.timestamp
    ++ (Alpha.encode message.symbol
    ++ (InstrumentTradingStatus.encode message.instrumentTradingStatus
    ++ (InstrumentTradingStatusReason.encode message.instrumentTradingStatusReason)))

def decode (bytes : List UInt8) : Option (InstrumentTradingStatusMessage × List UInt8) := do
  let (timestamp, bytes) ← decodeUInt 8 bytes
  let (symbol, bytes) ← Alpha.decode 8 bytes
  let (instrumentTradingStatus, bytes) ← InstrumentTradingStatus.decode bytes
  let (instrumentTradingStatusReason, bytes) ← InstrumentTradingStatusReason.decode bytes
  pure ({ timestamp, symbol, instrumentTradingStatus, instrumentTradingStatusReason }, bytes)

@[simp] theorem encode_length (message : InstrumentTradingStatusMessage) : (encode message).length = 18 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Alpha.encode_length, InstrumentTradingStatus.encode_length, InstrumentTradingStatusReason.encode_length]

theorem encode_length_pos (message : InstrumentTradingStatusMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : InstrumentTradingStatusMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, InstrumentTradingStatus.decode_encode, some_bind]
  dsimp only
  rw [InstrumentTradingStatusReason.decode_encode, some_bind]
  rfl

end InstrumentTradingStatusMessage

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

/-- Broken Trade Message: 36 bytes -/
structure BrokenTradeMessage where
  timestamp : BitVec 64
  symbol : Alpha 8
  tradeId : BitVec 64
  originalQuantity : BitVec 32
  originalPrice : BitVec 64
  deriving DecidableEq, Repr

namespace BrokenTradeMessage

def encode (message : BrokenTradeMessage) : List UInt8 :=
  encodeUInt 8 message.timestamp
    ++ (Alpha.encode message.symbol
    ++ (encodeUInt 8 message.tradeId
    ++ (encodeUInt 4 message.originalQuantity
    ++ (encodeUInt 8 message.originalPrice))))

def decode (bytes : List UInt8) : Option (BrokenTradeMessage × List UInt8) := do
  let (timestamp, bytes) ← decodeUInt 8 bytes
  let (symbol, bytes) ← Alpha.decode 8 bytes
  let (tradeId, bytes) ← decodeUInt 8 bytes
  let (originalQuantity, bytes) ← decodeUInt 4 bytes
  let (originalPrice, bytes) ← decodeUInt 8 bytes
  pure ({ timestamp, symbol, tradeId, originalQuantity, originalPrice }, bytes)

@[simp] theorem encode_length (message : BrokenTradeMessage) : (encode message).length = 36 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Alpha.encode_length]

theorem encode_length_pos (message : BrokenTradeMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : BrokenTradeMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end BrokenTradeMessage

/-- Corrected Trade Message: 48 bytes -/
structure CorrectedTradeMessage where
  timestamp : BitVec 64
  symbol : Alpha 8
  tradeId : BitVec 64
  originalQuantity : BitVec 32
  originalPrice : BitVec 64
  correctedQuantity : BitVec 32
  correctedPrice : BitVec 64
  deriving DecidableEq, Repr

namespace CorrectedTradeMessage

def encode (message : CorrectedTradeMessage) : List UInt8 :=
  encodeUInt 8 message.timestamp
    ++ (Alpha.encode message.symbol
    ++ (encodeUInt 8 message.tradeId
    ++ (encodeUInt 4 message.originalQuantity
    ++ (encodeUInt 8 message.originalPrice
    ++ (encodeUInt 4 message.correctedQuantity
    ++ (encodeUInt 8 message.correctedPrice))))))

def decode (bytes : List UInt8) : Option (CorrectedTradeMessage × List UInt8) := do
  let (timestamp, bytes) ← decodeUInt 8 bytes
  let (symbol, bytes) ← Alpha.decode 8 bytes
  let (tradeId, bytes) ← decodeUInt 8 bytes
  let (originalQuantity, bytes) ← decodeUInt 4 bytes
  let (originalPrice, bytes) ← decodeUInt 8 bytes
  let (correctedQuantity, bytes) ← decodeUInt 4 bytes
  let (correctedPrice, bytes) ← decodeUInt 8 bytes
  pure ({ timestamp, symbol, tradeId, originalQuantity, originalPrice, correctedQuantity, correctedPrice }, bytes)

@[simp] theorem encode_length (message : CorrectedTradeMessage) : (encode message).length = 48 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Alpha.encode_length]

theorem encode_length_pos (message : CorrectedTradeMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : CorrectedTradeMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
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
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end CorrectedTradeMessage

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

/-- Best Bid Offer Message: 48 bytes -/
structure BestBidOfferMessage where
  timestamp : BitVec 64
  symbol : Alpha 8
  totalBidSize : BitVec 32
  custBidSize : BitVec 32
  bidPrice : BitVec 64
  totalOfferSize : BitVec 32
  custOfferSize : BitVec 32
  offerPrice : BitVec 64
  deriving DecidableEq, Repr

namespace BestBidOfferMessage

def encode (message : BestBidOfferMessage) : List UInt8 :=
  encodeUInt 8 message.timestamp
    ++ (Alpha.encode message.symbol
    ++ (encodeUInt 4 message.totalBidSize
    ++ (encodeUInt 4 message.custBidSize
    ++ (encodeUInt 8 message.bidPrice
    ++ (encodeUInt 4 message.totalOfferSize
    ++ (encodeUInt 4 message.custOfferSize
    ++ (encodeUInt 8 message.offerPrice)))))))

def decode (bytes : List UInt8) : Option (BestBidOfferMessage × List UInt8) := do
  let (timestamp, bytes) ← decodeUInt 8 bytes
  let (symbol, bytes) ← Alpha.decode 8 bytes
  let (totalBidSize, bytes) ← decodeUInt 4 bytes
  let (custBidSize, bytes) ← decodeUInt 4 bytes
  let (bidPrice, bytes) ← decodeUInt 8 bytes
  let (totalOfferSize, bytes) ← decodeUInt 4 bytes
  let (custOfferSize, bytes) ← decodeUInt 4 bytes
  let (offerPrice, bytes) ← decodeUInt 8 bytes
  pure ({ timestamp, symbol, totalBidSize, custBidSize, bidPrice, totalOfferSize, custOfferSize, offerPrice }, bytes)

@[simp] theorem encode_length (message : BestBidOfferMessage) : (encode message).length = 48 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Alpha.encode_length]

theorem encode_length_pos (message : BestBidOfferMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : BestBidOfferMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
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

end BestBidOfferMessage

/-- Best Bid Message: 32 bytes -/
structure BestBidMessage where
  timestamp : BitVec 64
  symbol : Alpha 8
  totalBidSize : BitVec 32
  custBidSize : BitVec 32
  bidPrice : BitVec 64
  deriving DecidableEq, Repr

namespace BestBidMessage

def encode (message : BestBidMessage) : List UInt8 :=
  encodeUInt 8 message.timestamp
    ++ (Alpha.encode message.symbol
    ++ (encodeUInt 4 message.totalBidSize
    ++ (encodeUInt 4 message.custBidSize
    ++ (encodeUInt 8 message.bidPrice))))

def decode (bytes : List UInt8) : Option (BestBidMessage × List UInt8) := do
  let (timestamp, bytes) ← decodeUInt 8 bytes
  let (symbol, bytes) ← Alpha.decode 8 bytes
  let (totalBidSize, bytes) ← decodeUInt 4 bytes
  let (custBidSize, bytes) ← decodeUInt 4 bytes
  let (bidPrice, bytes) ← decodeUInt 8 bytes
  pure ({ timestamp, symbol, totalBidSize, custBidSize, bidPrice }, bytes)

@[simp] theorem encode_length (message : BestBidMessage) : (encode message).length = 32 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Alpha.encode_length]

theorem encode_length_pos (message : BestBidMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : BestBidMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end BestBidMessage

/-- Best Offer Message: 32 bytes -/
structure BestOfferMessage where
  timestamp : BitVec 64
  symbol : Alpha 8
  totalOfferSize : BitVec 32
  custOfferSize : BitVec 32
  offerPrice : BitVec 64
  deriving DecidableEq, Repr

namespace BestOfferMessage

def encode (message : BestOfferMessage) : List UInt8 :=
  encodeUInt 8 message.timestamp
    ++ (Alpha.encode message.symbol
    ++ (encodeUInt 4 message.totalOfferSize
    ++ (encodeUInt 4 message.custOfferSize
    ++ (encodeUInt 8 message.offerPrice))))

def decode (bytes : List UInt8) : Option (BestOfferMessage × List UInt8) := do
  let (timestamp, bytes) ← decodeUInt 8 bytes
  let (symbol, bytes) ← Alpha.decode 8 bytes
  let (totalOfferSize, bytes) ← decodeUInt 4 bytes
  let (custOfferSize, bytes) ← decodeUInt 4 bytes
  let (offerPrice, bytes) ← decodeUInt 8 bytes
  pure ({ timestamp, symbol, totalOfferSize, custOfferSize, offerPrice }, bytes)

@[simp] theorem encode_length (message : BestOfferMessage) : (encode message).length = 32 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Alpha.encode_length]

theorem encode_length_pos (message : BestOfferMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : BestOfferMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end BestOfferMessage

/-- Best Bid Short Message: 22 bytes -/
structure BestBidShortMessage where
  timestamp : BitVec 64
  symbol : Alpha 8
  totalBidSizeShort : BitVec 16
  custBidSizeShort : BitVec 16
  bidPriceShort : BitVec 16
  deriving DecidableEq, Repr

namespace BestBidShortMessage

def encode (message : BestBidShortMessage) : List UInt8 :=
  encodeUInt 8 message.timestamp
    ++ (Alpha.encode message.symbol
    ++ (encodeUInt 2 message.totalBidSizeShort
    ++ (encodeUInt 2 message.custBidSizeShort
    ++ (encodeUInt 2 message.bidPriceShort))))

def decode (bytes : List UInt8) : Option (BestBidShortMessage × List UInt8) := do
  let (timestamp, bytes) ← decodeUInt 8 bytes
  let (symbol, bytes) ← Alpha.decode 8 bytes
  let (totalBidSizeShort, bytes) ← decodeUInt 2 bytes
  let (custBidSizeShort, bytes) ← decodeUInt 2 bytes
  let (bidPriceShort, bytes) ← decodeUInt 2 bytes
  pure ({ timestamp, symbol, totalBidSizeShort, custBidSizeShort, bidPriceShort }, bytes)

@[simp] theorem encode_length (message : BestBidShortMessage) : (encode message).length = 22 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Alpha.encode_length]

theorem encode_length_pos (message : BestBidShortMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : BestBidShortMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end BestBidShortMessage

/-- Best Offer Short Message: 22 bytes -/
structure BestOfferShortMessage where
  timestamp : BitVec 64
  symbol : Alpha 8
  totalOfferSizeShort : BitVec 16
  custOfferSizeShort : BitVec 16
  offerPriceShort : BitVec 16
  deriving DecidableEq, Repr

namespace BestOfferShortMessage

def encode (message : BestOfferShortMessage) : List UInt8 :=
  encodeUInt 8 message.timestamp
    ++ (Alpha.encode message.symbol
    ++ (encodeUInt 2 message.totalOfferSizeShort
    ++ (encodeUInt 2 message.custOfferSizeShort
    ++ (encodeUInt 2 message.offerPriceShort))))

def decode (bytes : List UInt8) : Option (BestOfferShortMessage × List UInt8) := do
  let (timestamp, bytes) ← decodeUInt 8 bytes
  let (symbol, bytes) ← Alpha.decode 8 bytes
  let (totalOfferSizeShort, bytes) ← decodeUInt 2 bytes
  let (custOfferSizeShort, bytes) ← decodeUInt 2 bytes
  let (offerPriceShort, bytes) ← decodeUInt 2 bytes
  pure ({ timestamp, symbol, totalOfferSizeShort, custOfferSizeShort, offerPriceShort }, bytes)

@[simp] theorem encode_length (message : BestOfferShortMessage) : (encode message).length = 22 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Alpha.encode_length]

theorem encode_length_pos (message : BestOfferShortMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : BestOfferShortMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end BestOfferShortMessage

/-- Trade Message: 43 bytes -/
structure TradeMessage where
  timestamp : BitVec 64
  symbol : Alpha 8
  tradeId : BitVec 64
  tradeConditions : BitVec 8
  side : Side
  quantity : BitVec 32
  price : BitVec 64
  custQuantity : BitVec 32
  capacity : Capacity
  deriving DecidableEq, Repr

namespace TradeMessage

def encode (message : TradeMessage) : List UInt8 :=
  encodeUInt 8 message.timestamp
    ++ (Alpha.encode message.symbol
    ++ (encodeUInt 8 message.tradeId
    ++ (encodeUIntLE 1 message.tradeConditions
    ++ (Side.encode message.side
    ++ (encodeUInt 4 message.quantity
    ++ (encodeUInt 8 message.price
    ++ (encodeUInt 4 message.custQuantity
    ++ (Capacity.encode message.capacity))))))))

def decode (bytes : List UInt8) : Option (TradeMessage × List UInt8) := do
  let (timestamp, bytes) ← decodeUInt 8 bytes
  let (symbol, bytes) ← Alpha.decode 8 bytes
  let (tradeId, bytes) ← decodeUInt 8 bytes
  let (tradeConditions, bytes) ← decodeUIntLE 1 bytes
  let (side, bytes) ← Side.decode bytes
  let (quantity, bytes) ← decodeUInt 4 bytes
  let (price, bytes) ← decodeUInt 8 bytes
  let (custQuantity, bytes) ← decodeUInt 4 bytes
  let (capacity, bytes) ← Capacity.decode bytes
  pure ({ timestamp, symbol, tradeId, tradeConditions, side, quantity, price, custQuantity, capacity }, bytes)

@[simp] theorem encode_length (message : TradeMessage) : (encode message).length = 43 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Alpha.encode_length, encodeUIntLE_length, Side.encode_length, Capacity.encode_length]

theorem encode_length_pos (message : TradeMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : TradeMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Side.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [Capacity.decode_encode, some_bind]
  rfl

end TradeMessage

/-- Clear Book Message: 16 bytes -/
structure ClearBookMessage where
  timestamp : BitVec 64
  symbol : Alpha 8
  deriving DecidableEq, Repr

namespace ClearBookMessage

def encode (message : ClearBookMessage) : List UInt8 :=
  encodeUInt 8 message.timestamp
    ++ (Alpha.encode message.symbol)

def decode (bytes : List UInt8) : Option (ClearBookMessage × List UInt8) := do
  let (timestamp, bytes) ← decodeUInt 8 bytes
  let (symbol, bytes) ← Alpha.decode 8 bytes
  pure ({ timestamp, symbol }, bytes)

@[simp] theorem encode_length (message : ClearBookMessage) : (encode message).length = 16 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Alpha.encode_length]

theorem encode_length_pos (message : ClearBookMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : ClearBookMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end ClearBookMessage

/-- Any Payload, selected by Template Id -/
inductive Payload where
  | instrumentDirectoryMessage (message : InstrumentDirectoryMessage) -- 1
  | instrumentTradingStatusMessage (message : InstrumentTradingStatusMessage) -- 2
  | tradingSessionStatusMessage (message : TradingSessionStatusMessage) -- 3
  | brokenTradeMessage (message : BrokenTradeMessage) -- 5
  | correctedTradeMessage (message : CorrectedTradeMessage) -- 6
  | snapshotCompleteMessage (message : SnapshotCompleteMessage) -- 7
  | bestBidOfferMessage (message : BestBidOfferMessage) -- 10
  | bestBidMessage (message : BestBidMessage) -- 11
  | bestOfferMessage (message : BestOfferMessage) -- 12
  | bestBidShortMessage (message : BestBidShortMessage) -- 13
  | bestOfferShortMessage (message : BestOfferShortMessage) -- 14
  | tradeMessage (message : TradeMessage) -- 15
  | clearBookMessage (message : ClearBookMessage) -- 16
  deriving DecidableEq, Repr

namespace Payload

/-- The Template Id each message is sent under -/
def tag : Payload → BitVec 8
  | .instrumentDirectoryMessage _ => 1
  | .instrumentTradingStatusMessage _ => 2
  | .tradingSessionStatusMessage _ => 3
  | .brokenTradeMessage _ => 5
  | .correctedTradeMessage _ => 6
  | .snapshotCompleteMessage _ => 7
  | .bestBidOfferMessage _ => 10
  | .bestBidMessage _ => 11
  | .bestOfferMessage _ => 12
  | .bestBidShortMessage _ => 13
  | .bestOfferShortMessage _ => 14
  | .tradeMessage _ => 15
  | .clearBookMessage _ => 16

def encode : Payload → List UInt8
  | .instrumentDirectoryMessage message => InstrumentDirectoryMessage.encode message
  | .instrumentTradingStatusMessage message => InstrumentTradingStatusMessage.encode message
  | .tradingSessionStatusMessage message => TradingSessionStatusMessage.encode message
  | .brokenTradeMessage message => BrokenTradeMessage.encode message
  | .correctedTradeMessage message => CorrectedTradeMessage.encode message
  | .snapshotCompleteMessage message => SnapshotCompleteMessage.encode message
  | .bestBidOfferMessage message => BestBidOfferMessage.encode message
  | .bestBidMessage message => BestBidMessage.encode message
  | .bestOfferMessage message => BestOfferMessage.encode message
  | .bestBidShortMessage message => BestBidShortMessage.encode message
  | .bestOfferShortMessage message => BestOfferShortMessage.encode message
  | .tradeMessage message => TradeMessage.encode message
  | .clearBookMessage message => ClearBookMessage.encode message

/-- The most bytes any message's encoding can take -/
theorem encode_length_le (message : Payload) : (encode message).length ≤ 56 := by
  cases message with
  | instrumentDirectoryMessage inner =>
    simp only [encode, InstrumentDirectoryMessage.encode_length]
    omega
  | instrumentTradingStatusMessage inner =>
    simp only [encode, InstrumentTradingStatusMessage.encode_length]
    omega
  | tradingSessionStatusMessage inner =>
    simp only [encode, TradingSessionStatusMessage.encode_length]
    omega
  | brokenTradeMessage inner =>
    simp only [encode, BrokenTradeMessage.encode_length]
    omega
  | correctedTradeMessage inner =>
    simp only [encode, CorrectedTradeMessage.encode_length]
    omega
  | snapshotCompleteMessage inner =>
    simp only [encode, SnapshotCompleteMessage.encode_length]
    omega
  | bestBidOfferMessage inner =>
    simp only [encode, BestBidOfferMessage.encode_length]
    omega
  | bestBidMessage inner =>
    simp only [encode, BestBidMessage.encode_length]
    omega
  | bestOfferMessage inner =>
    simp only [encode, BestOfferMessage.encode_length]
    omega
  | bestBidShortMessage inner =>
    simp only [encode, BestBidShortMessage.encode_length]
    omega
  | bestOfferShortMessage inner =>
    simp only [encode, BestOfferShortMessage.encode_length]
    omega
  | tradeMessage inner =>
    simp only [encode, TradeMessage.encode_length]
    omega
  | clearBookMessage inner =>
    simp only [encode, ClearBookMessage.encode_length]
    omega

def decode (tag : BitVec 8) (bytes : List UInt8) : Option (Payload × List UInt8) :=
  if tag = 1 then (InstrumentDirectoryMessage.decode bytes).map fun (message, rest) => (.instrumentDirectoryMessage message, rest)
  else if tag = 2 then (InstrumentTradingStatusMessage.decode bytes).map fun (message, rest) => (.instrumentTradingStatusMessage message, rest)
  else if tag = 3 then (TradingSessionStatusMessage.decode bytes).map fun (message, rest) => (.tradingSessionStatusMessage message, rest)
  else if tag = 5 then (BrokenTradeMessage.decode bytes).map fun (message, rest) => (.brokenTradeMessage message, rest)
  else if tag = 6 then (CorrectedTradeMessage.decode bytes).map fun (message, rest) => (.correctedTradeMessage message, rest)
  else if tag = 7 then (SnapshotCompleteMessage.decode bytes).map fun (message, rest) => (.snapshotCompleteMessage message, rest)
  else if tag = 10 then (BestBidOfferMessage.decode bytes).map fun (message, rest) => (.bestBidOfferMessage message, rest)
  else if tag = 11 then (BestBidMessage.decode bytes).map fun (message, rest) => (.bestBidMessage message, rest)
  else if tag = 12 then (BestOfferMessage.decode bytes).map fun (message, rest) => (.bestOfferMessage message, rest)
  else if tag = 13 then (BestBidShortMessage.decode bytes).map fun (message, rest) => (.bestBidShortMessage message, rest)
  else if tag = 14 then (BestOfferShortMessage.decode bytes).map fun (message, rest) => (.bestOfferShortMessage message, rest)
  else if tag = 15 then (TradeMessage.decode bytes).map fun (message, rest) => (.tradeMessage message, rest)
  else if tag = 16 then (ClearBookMessage.decode bytes).map fun (message, rest) => (.clearBookMessage message, rest)
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
theorem encode_length_le (message : SbeMessage) : (encode message).length ≤ 62 := by
  unfold encode
  cases message.payload with
  | instrumentDirectoryMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, InstrumentDirectoryMessage.encode_length]
    omega
  | instrumentTradingStatusMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, InstrumentTradingStatusMessage.encode_length]
    omega
  | tradingSessionStatusMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, TradingSessionStatusMessage.encode_length]
    omega
  | brokenTradeMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, BrokenTradeMessage.encode_length]
    omega
  | correctedTradeMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, CorrectedTradeMessage.encode_length]
    omega
  | snapshotCompleteMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, SnapshotCompleteMessage.encode_length]
    omega
  | bestBidOfferMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, BestBidOfferMessage.encode_length]
    omega
  | bestBidMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, BestBidMessage.encode_length]
    omega
  | bestOfferMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, BestOfferMessage.encode_length]
    omega
  | bestBidShortMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, BestBidShortMessage.encode_length]
    omega
  | bestOfferShortMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, BestOfferShortMessage.encode_length]
    omega
  | tradeMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, TradeMessage.encode_length]
    omega
  | clearBookMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, ClearBookMessage.encode_length]
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
  | heartbeat (message : Heartbeat) -- 0
  | sessionShutdown (message : SessionShutdown) -- 1
  | sequencedMessage (message : SequencedMessage) -- 2
  deriving DecidableEq, Repr

namespace SequencedMessages

/-- The Message Type each message is sent under -/
def tag : SequencedMessages → BitVec 8
  | .heartbeat _ => 0
  | .sessionShutdown _ => 1
  | .sequencedMessage _ => 2

def encode : SequencedMessages → List UInt8
  | .heartbeat message => Heartbeat.encode message
  | .sessionShutdown message => SessionShutdown.encode message
  | .sequencedMessage message => SequencedMessage.encode message

def decode (tag : BitVec 8) (bytes : List UInt8) : Option (SequencedMessages × List UInt8) :=
  if tag = 0 then (Heartbeat.decode bytes).map fun (message, rest) => (.heartbeat message, rest)
  else if tag = 1 then (SessionShutdown.decode bytes).map fun (message, rest) => (.sessionShutdown message, rest)
  else if tag = 2 then (SequencedMessage.decode bytes).map fun (message, rest) => (.sequencedMessage message, rest)
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

end Omi.MemxMemxoptionsMemoirtopSbeV13
