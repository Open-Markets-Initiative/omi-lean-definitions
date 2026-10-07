import Wire

/-!
# London Stock Exchange  v11.9

Generated from the binary model, with the proofs the model's rules call for: every record
decodes back to what was encoded; a message dispatch selects the message its type names;
a count is written from the list it counts; a length prefix is written from the bytes it frames;
and a packet read to the end of its data decodes to the messages that were written.

Note: Snapshot Complete Flags is a bit field set, proven as its 1 byte integer rather than bit by bit.

Note: Symbol Status Flags is a bit field set, proven as its 1 byte integer rather than bit by bit.

Note: Add Order Flags is a bit field set, proven as its 1 byte integer rather than bit by bit.

Note: Add Attributed Order Flags is a bit field set, proven as its 1 byte integer rather than bit by bit.

Note: Tcp Unit's Length is written from its body but not checked on decode, since the body has no bound the prefix must fit; the body is read by its content.

Text fields are kept byte for byte, padding included, so what is decoded encodes back unchanged.
Prices with implied decimals are proven as the integers on the wire.
-/

namespace Omi.LsegMillenniumLevel2recoveryMitchV119

/-- Login Status: one byte code -/
def LoginStatus.codes : List UInt8 :=
  [0x41, 0x61, 0x62, 0x63, 0x64, 0x65]

inductive LoginStatus where
  | loginAccepted -- Login Accepted
  | compIdInactiveLocked -- Comp Id Inactive Locked
  | loginLimitReached -- Login Limit Reached
  | serviceUnavailable -- Service Unavailable
  | concurrentLimitReached -- Concurrent Limit Reached
  | failedOther -- Failed Other
  | unlisted (byte : { byte : UInt8 // byte ∉ LoginStatus.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace LoginStatus

def toByte : LoginStatus → UInt8
  | .loginAccepted => 0x41
  | .compIdInactiveLocked => 0x61
  | .loginLimitReached => 0x62
  | .serviceUnavailable => 0x63
  | .concurrentLimitReached => 0x64
  | .failedOther => 0x65
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : LoginStatus :=
  if byte = 0x41 then .loginAccepted
  else if byte = 0x61 then .compIdInactiveLocked
  else if byte = 0x62 then .loginLimitReached
  else if byte = 0x63 then .serviceUnavailable
  else if byte = 0x64 then .concurrentLimitReached
  else .failedOther

def ofByte (byte : UInt8) : LoginStatus :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : LoginStatus) : ofByte value.toByte = value := by
  cases value with
  | loginAccepted => decide
  | compIdInactiveLocked => decide
  | loginLimitReached => decide
  | serviceUnavailable => decide
  | concurrentLimitReached => decide
  | failedOther => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : LoginStatus) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (LoginStatus × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : LoginStatus) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : LoginStatus) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end LoginStatus

/-- Snapshot Status: one byte code -/
def SnapshotStatus.codes : List UInt8 :=
  [0x41, 0x4F, 0x55, 0x61, 0x62, 0x63, 0x64, 0x65]

inductive SnapshotStatus where
  | requestAccepted -- Request Accepted
  | outOfRange -- Out Of Range
  | snapshotUnavailable -- Snapshot Unavailable
  | validSegmentOrSymbolNotSpecified -- Valid Segment Or Symbol Not Specified
  | requestLimitReached -- Request Limit Reached
  | concurrentLimitReached -- Concurrent Limit Reached
  | unsupportedMessageType -- Unsupported Message Type
  | failedOther -- Failed Other
  | unlisted (byte : { byte : UInt8 // byte ∉ SnapshotStatus.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace SnapshotStatus

def toByte : SnapshotStatus → UInt8
  | .requestAccepted => 0x41
  | .outOfRange => 0x4F
  | .snapshotUnavailable => 0x55
  | .validSegmentOrSymbolNotSpecified => 0x61
  | .requestLimitReached => 0x62
  | .concurrentLimitReached => 0x63
  | .unsupportedMessageType => 0x64
  | .failedOther => 0x65
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : SnapshotStatus :=
  if byte = 0x41 then .requestAccepted
  else if byte = 0x4F then .outOfRange
  else if byte = 0x55 then .snapshotUnavailable
  else if byte = 0x61 then .validSegmentOrSymbolNotSpecified
  else if byte = 0x62 then .requestLimitReached
  else if byte = 0x63 then .concurrentLimitReached
  else if byte = 0x64 then .unsupportedMessageType
  else .failedOther

def ofByte (byte : UInt8) : SnapshotStatus :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : SnapshotStatus) : ofByte value.toByte = value := by
  cases value with
  | requestAccepted => decide
  | outOfRange => decide
  | snapshotUnavailable => decide
  | validSegmentOrSymbolNotSpecified => decide
  | requestLimitReached => decide
  | concurrentLimitReached => decide
  | unsupportedMessageType => decide
  | failedOther => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : SnapshotStatus) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (SnapshotStatus × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : SnapshotStatus) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : SnapshotStatus) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end SnapshotStatus

/-- Trading Status: one byte code -/
def TradingStatus.codes : List UInt8 :=
  [0x20, 0x48, 0x54, 0x61, 0x62, 0x63, 0x64, 0x65, 0x66, 0x6C, 0x6D, 0x6E, 0x6F, 0x71, 0x72, 0x74, 0x77, 0x78, 0x75, 0x47]

inductive TradingStatus where
  | active -- Active
  | halt -- Halt
  | regularTradingStartOfTradeReporting -- Regular Trading Start Of Trade Reporting
  | openingFirstAuctionCall -- Opening First Auction Call
  | postClose -- Post Close
  | marketCloseSystemShutdown -- Market Close System Shutdown
  | closingAuctionCall -- Closing Auction Call
  | aespAuctionCall -- Aesp Auction Call
  | resumeAuctionCall -- Resume Auction Call
  | pause -- Pause
  | preMandatory -- Pre Mandatory
  | mandatory -- Mandatory
  | postMandatory -- Post Mandatory
  | edspAuctionCall -- Edsp Auction Call
  | periodicAuctionCall -- Periodic Auction Call
  | endTradeReporting -- End Trade Reporting
  | noActiveSession -- No Active Session
  | endOfPostClose -- End Of Post Close
  | closingPriceCrossing -- Closing Price Crossing
  | scheduledLevel1OnlyAuction -- Scheduled Level 1 Only Auction
  | unlisted (byte : { byte : UInt8 // byte ∉ TradingStatus.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace TradingStatus

def toByte : TradingStatus → UInt8
  | .active => 0x20
  | .halt => 0x48
  | .regularTradingStartOfTradeReporting => 0x54
  | .openingFirstAuctionCall => 0x61
  | .postClose => 0x62
  | .marketCloseSystemShutdown => 0x63
  | .closingAuctionCall => 0x64
  | .aespAuctionCall => 0x65
  | .resumeAuctionCall => 0x66
  | .pause => 0x6C
  | .preMandatory => 0x6D
  | .mandatory => 0x6E
  | .postMandatory => 0x6F
  | .edspAuctionCall => 0x71
  | .periodicAuctionCall => 0x72
  | .endTradeReporting => 0x74
  | .noActiveSession => 0x77
  | .endOfPostClose => 0x78
  | .closingPriceCrossing => 0x75
  | .scheduledLevel1OnlyAuction => 0x47
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : TradingStatus :=
  if byte = 0x20 then .active
  else if byte = 0x48 then .halt
  else if byte = 0x54 then .regularTradingStartOfTradeReporting
  else if byte = 0x61 then .openingFirstAuctionCall
  else if byte = 0x62 then .postClose
  else if byte = 0x63 then .marketCloseSystemShutdown
  else if byte = 0x64 then .closingAuctionCall
  else if byte = 0x65 then .aespAuctionCall
  else if byte = 0x66 then .resumeAuctionCall
  else if byte = 0x6C then .pause
  else if byte = 0x6D then .preMandatory
  else if byte = 0x6E then .mandatory
  else if byte = 0x6F then .postMandatory
  else if byte = 0x71 then .edspAuctionCall
  else if byte = 0x72 then .periodicAuctionCall
  else if byte = 0x74 then .endTradeReporting
  else if byte = 0x77 then .noActiveSession
  else if byte = 0x78 then .endOfPostClose
  else if byte = 0x75 then .closingPriceCrossing
  else .scheduledLevel1OnlyAuction

def ofByte (byte : UInt8) : TradingStatus :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : TradingStatus) : ofByte value.toByte = value := by
  cases value with
  | active => decide
  | halt => decide
  | regularTradingStartOfTradeReporting => decide
  | openingFirstAuctionCall => decide
  | postClose => decide
  | marketCloseSystemShutdown => decide
  | closingAuctionCall => decide
  | aespAuctionCall => decide
  | resumeAuctionCall => decide
  | pause => decide
  | preMandatory => decide
  | mandatory => decide
  | postMandatory => decide
  | edspAuctionCall => decide
  | periodicAuctionCall => decide
  | endTradeReporting => decide
  | noActiveSession => decide
  | endOfPostClose => decide
  | closingPriceCrossing => decide
  | scheduledLevel1OnlyAuction => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : TradingStatus) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (TradingStatus × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : TradingStatus) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : TradingStatus) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end TradingStatus

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

/-- Login Request Message: 16 bytes -/
structure LoginRequestMessage where
  username : Alpha 6
  password : Alpha 10
  deriving DecidableEq, Repr

namespace LoginRequestMessage

def encode (message : LoginRequestMessage) : List UInt8 :=
  Alpha.encode message.username
    ++ (Alpha.encode message.password)

def decode (bytes : List UInt8) : Option (LoginRequestMessage × List UInt8) := do
  let (username, bytes) ← Alpha.decode 6 bytes
  let (password, bytes) ← Alpha.decode 10 bytes
  pure ({ username, password }, bytes)

@[simp] theorem encode_length (message : LoginRequestMessage) : (encode message).length = 16 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length]

theorem encode_length_pos (message : LoginRequestMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : LoginRequestMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end LoginRequestMessage

/-- Login Response Message: 1 bytes -/
structure LoginResponseMessage where
  loginStatus : LoginStatus
  deriving DecidableEq, Repr

namespace LoginResponseMessage

def encode (message : LoginResponseMessage) : List UInt8 :=
  LoginStatus.encode message.loginStatus

def decode (bytes : List UInt8) : Option (LoginResponseMessage × List UInt8) := do
  let (loginStatus, bytes) ← LoginStatus.decode bytes
  pure ({ loginStatus }, bytes)

@[simp] theorem encode_length (message : LoginResponseMessage) : (encode message).length = 1 := by
  unfold encode
  simp only [LoginStatus.encode_length]

theorem encode_length_pos (message : LoginResponseMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : LoginResponseMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [LoginStatus.decode_encode, some_bind]
  rfl

end LoginResponseMessage

/-- Snapshot Request Message: 14 bytes -/
structure SnapshotRequestMessage where
  sequenceNumber : BitVec 32
  segment : Alpha 6
  instrumentId : BitVec 32
  deriving DecidableEq, Repr

namespace SnapshotRequestMessage

def encode (message : SnapshotRequestMessage) : List UInt8 :=
  encodeUIntLE 4 message.sequenceNumber
    ++ (Alpha.encode message.segment
    ++ (encodeUIntLE 4 message.instrumentId))

def decode (bytes : List UInt8) : Option (SnapshotRequestMessage × List UInt8) := do
  let (sequenceNumber, bytes) ← decodeUIntLE 4 bytes
  let (segment, bytes) ← Alpha.decode 6 bytes
  let (instrumentId, bytes) ← decodeUIntLE 4 bytes
  pure ({ sequenceNumber, segment, instrumentId }, bytes)

@[simp] theorem encode_length (message : SnapshotRequestMessage) : (encode message).length = 14 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length]

theorem encode_length_pos (message : SnapshotRequestMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SnapshotRequestMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end SnapshotRequestMessage

/-- Snapshot Response Message: 9 bytes -/
structure SnapshotResponseMessage where
  sequenceNumber : BitVec 32
  orderCount : BitVec 32
  snapshotStatus : SnapshotStatus
  deriving DecidableEq, Repr

namespace SnapshotResponseMessage

def encode (message : SnapshotResponseMessage) : List UInt8 :=
  encodeUIntLE 4 message.sequenceNumber
    ++ (encodeUIntLE 4 message.orderCount
    ++ (SnapshotStatus.encode message.snapshotStatus))

def decode (bytes : List UInt8) : Option (SnapshotResponseMessage × List UInt8) := do
  let (sequenceNumber, bytes) ← decodeUIntLE 4 bytes
  let (orderCount, bytes) ← decodeUIntLE 4 bytes
  let (snapshotStatus, bytes) ← SnapshotStatus.decode bytes
  pure ({ sequenceNumber, orderCount, snapshotStatus }, bytes)

@[simp] theorem encode_length (message : SnapshotResponseMessage) : (encode message).length = 9 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, SnapshotStatus.encode_length]

theorem encode_length_pos (message : SnapshotResponseMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SnapshotResponseMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [SnapshotStatus.decode_encode, some_bind]
  rfl

end SnapshotResponseMessage

/-- Snapshot Complete Message: 15 bytes -/
structure SnapshotCompleteMessage where
  sequenceNumber : BitVec 32
  segment : Alpha 6
  instrumentId : BitVec 32
  snapshotCompleteFlags : BitVec 8
  deriving DecidableEq, Repr

namespace SnapshotCompleteMessage

def encode (message : SnapshotCompleteMessage) : List UInt8 :=
  encodeUIntLE 4 message.sequenceNumber
    ++ (Alpha.encode message.segment
    ++ (encodeUIntLE 4 message.instrumentId
    ++ (encodeUIntLE 1 message.snapshotCompleteFlags)))

def decode (bytes : List UInt8) : Option (SnapshotCompleteMessage × List UInt8) := do
  let (sequenceNumber, bytes) ← decodeUIntLE 4 bytes
  let (segment, bytes) ← Alpha.decode 6 bytes
  let (instrumentId, bytes) ← decodeUIntLE 4 bytes
  let (snapshotCompleteFlags, bytes) ← decodeUIntLE 1 bytes
  pure ({ sequenceNumber, segment, instrumentId, snapshotCompleteFlags }, bytes)

@[simp] theorem encode_length (message : SnapshotCompleteMessage) : (encode message).length = 15 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length]

theorem encode_length_pos (message : SnapshotCompleteMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SnapshotCompleteMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end SnapshotCompleteMessage

/-- Symbol Status Message: 26 bytes -/
structure SymbolStatusMessage where
  nanosecond : BitVec 32
  instrumentId : BitVec 32
  reservedA : Alpha 1
  reservedB : Alpha 1
  tradingStatus : TradingStatus
  symbolStatusFlags : BitVec 8
  reason : Alpha 4
  sessionChangeReason : BitVec 8
  newEndTime : Alpha 8
  bookType : BitVec 8
  deriving DecidableEq, Repr

namespace SymbolStatusMessage

def encode (message : SymbolStatusMessage) : List UInt8 :=
  encodeUIntLE 4 message.nanosecond
    ++ (encodeUIntLE 4 message.instrumentId
    ++ (Alpha.encode message.reservedA
    ++ (Alpha.encode message.reservedB
    ++ (TradingStatus.encode message.tradingStatus
    ++ (encodeUIntLE 1 message.symbolStatusFlags
    ++ (Alpha.encode message.reason
    ++ (encodeUIntLE 1 message.sessionChangeReason
    ++ (Alpha.encode message.newEndTime
    ++ (encodeUIntLE 1 message.bookType)))))))))

def decode (bytes : List UInt8) : Option (SymbolStatusMessage × List UInt8) := do
  let (nanosecond, bytes) ← decodeUIntLE 4 bytes
  let (instrumentId, bytes) ← decodeUIntLE 4 bytes
  let (reservedA, bytes) ← Alpha.decode 1 bytes
  let (reservedB, bytes) ← Alpha.decode 1 bytes
  let (tradingStatus, bytes) ← TradingStatus.decode bytes
  let (symbolStatusFlags, bytes) ← decodeUIntLE 1 bytes
  let (reason, bytes) ← Alpha.decode 4 bytes
  let (sessionChangeReason, bytes) ← decodeUIntLE 1 bytes
  let (newEndTime, bytes) ← Alpha.decode 8 bytes
  let (bookType, bytes) ← decodeUIntLE 1 bytes
  pure ({ nanosecond, instrumentId, reservedA, reservedB, tradingStatus, symbolStatusFlags, reason, sessionChangeReason, newEndTime, bookType }, bytes)

@[simp] theorem encode_length (message : SymbolStatusMessage) : (encode message).length = 26 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length, TradingStatus.encode_length]

theorem encode_length_pos (message : SymbolStatusMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SymbolStatusMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, TradingStatus.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end SymbolStatusMessage

/-- Add Order Message: 42 bytes -/
structure AddOrderMessage where
  nanosecond : BitVec 32
  orderId : BitVec 64
  side : Side
  quantity : BitVec 32
  instrumentId : BitVec 32
  reservedA : Alpha 1
  reservedB : Alpha 1
  price : BitVec 64
  addOrderFlags : BitVec 8
  reserved10 : Alpha 10
  deriving DecidableEq, Repr

namespace AddOrderMessage

def encode (message : AddOrderMessage) : List UInt8 :=
  encodeUIntLE 4 message.nanosecond
    ++ (encodeUIntLE 8 message.orderId
    ++ (Side.encode message.side
    ++ (encodeUIntLE 4 message.quantity
    ++ (encodeUIntLE 4 message.instrumentId
    ++ (Alpha.encode message.reservedA
    ++ (Alpha.encode message.reservedB
    ++ (encodeUIntLE 8 message.price
    ++ (encodeUIntLE 1 message.addOrderFlags
    ++ (Alpha.encode message.reserved10)))))))))

def decode (bytes : List UInt8) : Option (AddOrderMessage × List UInt8) := do
  let (nanosecond, bytes) ← decodeUIntLE 4 bytes
  let (orderId, bytes) ← decodeUIntLE 8 bytes
  let (side, bytes) ← Side.decode bytes
  let (quantity, bytes) ← decodeUIntLE 4 bytes
  let (instrumentId, bytes) ← decodeUIntLE 4 bytes
  let (reservedA, bytes) ← Alpha.decode 1 bytes
  let (reservedB, bytes) ← Alpha.decode 1 bytes
  let (price, bytes) ← decodeUIntLE 8 bytes
  let (addOrderFlags, bytes) ← decodeUIntLE 1 bytes
  let (reserved10, bytes) ← Alpha.decode 10 bytes
  pure ({ nanosecond, orderId, side, quantity, instrumentId, reservedA, reservedB, price, addOrderFlags, reserved10 }, bytes)

@[simp] theorem encode_length (message : AddOrderMessage) : (encode message).length = 42 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Side.encode_length, Alpha.encode_length]

theorem encode_length_pos (message : AddOrderMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : AddOrderMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Side.decode_encode, some_bind]
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
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end AddOrderMessage

/-- Add Attributed Order Message: 43 bytes -/
structure AddAttributedOrderMessage where
  nanosecond : BitVec 32
  orderId : BitVec 64
  side : Side
  quantity : BitVec 32
  instrumentId : BitVec 32
  reservedA : Alpha 1
  reservedB : Alpha 1
  price : BitVec 64
  attribution : Alpha 11
  addAttributedOrderFlags : BitVec 8
  deriving DecidableEq, Repr

namespace AddAttributedOrderMessage

def encode (message : AddAttributedOrderMessage) : List UInt8 :=
  encodeUIntLE 4 message.nanosecond
    ++ (encodeUIntLE 8 message.orderId
    ++ (Side.encode message.side
    ++ (encodeUIntLE 4 message.quantity
    ++ (encodeUIntLE 4 message.instrumentId
    ++ (Alpha.encode message.reservedA
    ++ (Alpha.encode message.reservedB
    ++ (encodeUIntLE 8 message.price
    ++ (Alpha.encode message.attribution
    ++ (encodeUIntLE 1 message.addAttributedOrderFlags)))))))))

def decode (bytes : List UInt8) : Option (AddAttributedOrderMessage × List UInt8) := do
  let (nanosecond, bytes) ← decodeUIntLE 4 bytes
  let (orderId, bytes) ← decodeUIntLE 8 bytes
  let (side, bytes) ← Side.decode bytes
  let (quantity, bytes) ← decodeUIntLE 4 bytes
  let (instrumentId, bytes) ← decodeUIntLE 4 bytes
  let (reservedA, bytes) ← Alpha.decode 1 bytes
  let (reservedB, bytes) ← Alpha.decode 1 bytes
  let (price, bytes) ← decodeUIntLE 8 bytes
  let (attribution, bytes) ← Alpha.decode 11 bytes
  let (addAttributedOrderFlags, bytes) ← decodeUIntLE 1 bytes
  pure ({ nanosecond, orderId, side, quantity, instrumentId, reservedA, reservedB, price, attribution, addAttributedOrderFlags }, bytes)

@[simp] theorem encode_length (message : AddAttributedOrderMessage) : (encode message).length = 43 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Side.encode_length, Alpha.encode_length]

theorem encode_length_pos (message : AddAttributedOrderMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : AddAttributedOrderMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Side.decode_encode, some_bind]
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
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end AddAttributedOrderMessage

/-- Any Payload, selected by Message Type -/
inductive Payload where
  | loginRequestMessage (message : LoginRequestMessage) -- 1
  | loginResponseMessage (message : LoginResponseMessage) -- 2
  | snapshotRequestMessage (message : SnapshotRequestMessage) -- 129
  | snapshotResponseMessage (message : SnapshotResponseMessage) -- 130
  | snapshotCompleteMessage (message : SnapshotCompleteMessage) -- 131
  | symbolStatusMessage (message : SymbolStatusMessage) -- 72
  | addOrderMessage (message : AddOrderMessage) -- 65
  | addAttributedOrderMessage (message : AddAttributedOrderMessage) -- 70
  deriving DecidableEq, Repr

namespace Payload

/-- The Message Type each message is sent under -/
def tag : Payload → BitVec 8
  | .loginRequestMessage _ => 1
  | .loginResponseMessage _ => 2
  | .snapshotRequestMessage _ => 129
  | .snapshotResponseMessage _ => 130
  | .snapshotCompleteMessage _ => 131
  | .symbolStatusMessage _ => 72
  | .addOrderMessage _ => 65
  | .addAttributedOrderMessage _ => 70

def encode : Payload → List UInt8
  | .loginRequestMessage message => LoginRequestMessage.encode message
  | .loginResponseMessage message => LoginResponseMessage.encode message
  | .snapshotRequestMessage message => SnapshotRequestMessage.encode message
  | .snapshotResponseMessage message => SnapshotResponseMessage.encode message
  | .snapshotCompleteMessage message => SnapshotCompleteMessage.encode message
  | .symbolStatusMessage message => SymbolStatusMessage.encode message
  | .addOrderMessage message => AddOrderMessage.encode message
  | .addAttributedOrderMessage message => AddAttributedOrderMessage.encode message

/-- The most bytes any message's encoding can take -/
theorem encode_length_le (message : Payload) : (encode message).length ≤ 43 := by
  cases message with
  | loginRequestMessage inner =>
    simp only [encode, LoginRequestMessage.encode_length]
    omega
  | loginResponseMessage inner =>
    simp only [encode, LoginResponseMessage.encode_length]
    omega
  | snapshotRequestMessage inner =>
    simp only [encode, SnapshotRequestMessage.encode_length]
    omega
  | snapshotResponseMessage inner =>
    simp only [encode, SnapshotResponseMessage.encode_length]
    omega
  | snapshotCompleteMessage inner =>
    simp only [encode, SnapshotCompleteMessage.encode_length]
    omega
  | symbolStatusMessage inner =>
    simp only [encode, SymbolStatusMessage.encode_length]
    omega
  | addOrderMessage inner =>
    simp only [encode, AddOrderMessage.encode_length]
    omega
  | addAttributedOrderMessage inner =>
    simp only [encode, AddAttributedOrderMessage.encode_length]
    omega

def decode (tag : BitVec 8) (bytes : List UInt8) : Option (Payload × List UInt8) :=
  if tag = 1 then (LoginRequestMessage.decode bytes).map fun (message, rest) => (.loginRequestMessage message, rest)
  else if tag = 2 then (LoginResponseMessage.decode bytes).map fun (message, rest) => (.loginResponseMessage message, rest)
  else if tag = 129 then (SnapshotRequestMessage.decode bytes).map fun (message, rest) => (.snapshotRequestMessage message, rest)
  else if tag = 130 then (SnapshotResponseMessage.decode bytes).map fun (message, rest) => (.snapshotResponseMessage message, rest)
  else if tag = 131 then (SnapshotCompleteMessage.decode bytes).map fun (message, rest) => (.snapshotCompleteMessage message, rest)
  else if tag = 72 then (SymbolStatusMessage.decode bytes).map fun (message, rest) => (.symbolStatusMessage message, rest)
  else if tag = 65 then (AddOrderMessage.decode bytes).map fun (message, rest) => (.addOrderMessage message, rest)
  else if tag = 70 then (AddAttributedOrderMessage.decode bytes).map fun (message, rest) => (.addAttributedOrderMessage message, rest)
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
theorem encodeBody_length_lt (message : Message) : (encodeBody message).length + 1 < 256 ^ 1 := by
  unfold encodeBody
  cases message.payload with
  | loginRequestMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, LoginRequestMessage.encode_length]
    omega
  | loginResponseMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, LoginResponseMessage.encode_length]
    omega
  | snapshotRequestMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, SnapshotRequestMessage.encode_length]
    omega
  | snapshotResponseMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, SnapshotResponseMessage.encode_length]
    omega
  | snapshotCompleteMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, SnapshotCompleteMessage.encode_length]
    omega
  | symbolStatusMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, SymbolStatusMessage.encode_length]
    omega
  | addOrderMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, AddOrderMessage.encode_length]
    omega
  | addAttributedOrderMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, AddAttributedOrderMessage.encode_length]
    omega

/-- Size rule: Message Length counts the bytes after it plus 1, so it is written from the body and checked on decode -/
def encode : Message → List UInt8 :=
  encodeFramedLE 1 1 encodeBody

def decode : List UInt8 → Option (Message × List UInt8) :=
  decodeFramedLE 1 1 decodeBody

@[simp] theorem decode_encode (message : Message) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) :=
  decodeFramedLE_encodeFramedLE 1 1 encodeBody decodeBody message (decodeBody_encodeBody message) (encodeBody_length_lt message) rest

theorem encode_length_pos (message : Message) : (encode message).length > 0 := by
  unfold encode
  rw [encodeFramedLE_length]
  omega

end Message

/-- Tcp Unit -/
structure TcpUnit where
  marketDataGroup : Alpha 1
  sequenceNumber : BitVec 32
  message : Bounded 1 Message
  deriving DecidableEq, Repr

namespace TcpUnit

def encodeBody (message : TcpUnit) : List UInt8 :=
  encodeUIntLE 1 (BitVec.ofNat (8 * 1) message.message.val.length)
    ++ (Alpha.encode message.marketDataGroup
    ++ (encodeUIntLE 4 message.sequenceNumber
    ++ (encodeMany Message.encode message.message.val)))

def decodeBody (bytes : List UInt8) : Option (TcpUnit × List UInt8) := do
  let (messageCount, bytes) ← decodeUIntLE 1 bytes
  let (marketDataGroup, bytes) ← Alpha.decode 1 bytes
  let (sequenceNumber, bytes) ← decodeUIntLE 4 bytes
  let (message_, bytes) ← decodeMany Message.decode messageCount.toNat bytes
  if fits_message : message_.length < 256 ^ 1 then
    pure ({ marketDataGroup, sequenceNumber, message := ⟨message_, fits_message⟩ }, bytes)
  else none

theorem decodeBody_encodeBody (message : TcpUnit) (rest : List UInt8) :
    decodeBody (encodeBody message ++ rest) = some (message, rest) := by
  unfold decodeBody encodeBody
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeMany_bounded 1 Message.encode Message.decode Message.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.message.length_lt]
  rfl

/-- Size rule: Length counts the bytes after it plus 2, so it is written from the body; the body has no bound the prefix must fit, so it is read by its content and the prefix is not checked -/
def encode (message : TcpUnit) : List UInt8 :=
  encodeUIntLE 2 (BitVec.ofNat (8 * 2) ((encodeBody message).length + 2)) ++ encodeBody message

def decode (bytes : List UInt8) : Option (TcpUnit × List UInt8) := do
  let (_, bytes) ← decodeUIntLE 2 bytes
  decodeBody bytes

@[simp] theorem decode_encode (message : TcpUnit) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  exact decodeBody_encodeBody message rest

theorem encode_length_pos (message : TcpUnit) : (encode message).length > 0 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length]
  omega

end TcpUnit

/-- Packet -/
structure Packet where
  tcpUnit : List TcpUnit
  deriving DecidableEq, Repr

namespace Packet

def encode (message : Packet) : List UInt8 :=
  encodeMany TcpUnit.encode message.tcpUnit

def decode (bytes : List UInt8) : Option Packet := do
  let tcpUnit ← decodeAll TcpUnit.decode bytes.length bytes
  pure { tcpUnit }

theorem decode_encode (message : Packet) : decode (encode message) = some message := by
  unfold decode encode
  rw [decodeAll_encodeMany TcpUnit.encode TcpUnit.decode TcpUnit.decode_encode TcpUnit.encode_length_pos message.tcpUnit _ (encodeMany_length_ge TcpUnit.encode TcpUnit.encode_length_pos message.tcpUnit), some_bind]
  rfl

end Packet

end Omi.LsegMillenniumLevel2recoveryMitchV119
