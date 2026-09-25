import Omi.Wire

/-!
# Miami International Holdings Express Interface v1.0.c

Generated from the binary model, with the proofs the model's rules call for: every record
decodes back to what was encoded; a message dispatch selects the message its type names;
a count is written from the list it counts; a length prefix is written from the bytes it frames;
and a packet read to the end of its data decodes to the messages that were written.

Note: Order Instructions is a bit field set, proven as its 2 byte integer rather than bit by bit.

Note: Self Trade Protection is a bit field set, proven as its 1 byte integer rather than bit by bit.

Note: Additional Order Indicators is a bit field set, proven as its 1 byte integer rather than bit by bit.

Note: Sequenced Data Packet is not framed: its length Sesm Packet Length is not an integer it reads.

Note: Unsequenced Data Packet is not framed: its length Sesm Packet Length is not an integer it reads.

Text fields are kept byte for byte, padding included, so what is decoded encodes back unchanged.
Prices with implied decimals are proven as the integers on the wire.
-/

namespace Omi.MiaxOnyxfuturesExpressinterfaceFeiV10C

/-- Time In Force: one byte code -/
def TimeInForce.codes : List UInt8 :=
  [0x49, 0x44, 0x46, 0x43, 0x58]

inductive TimeInForce where
  | ioc -- Ioc
  | day -- Day
  | fok -- Fok
  | gtc -- Gtc
  | gtd -- Gtd
  | unlisted (byte : { byte : UInt8 // byte ∉ TimeInForce.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace TimeInForce

def toByte : TimeInForce → UInt8
  | .ioc => 0x49
  | .day => 0x44
  | .fok => 0x46
  | .gtc => 0x43
  | .gtd => 0x58
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : TimeInForce :=
  if byte = 0x49 then .ioc
  else if byte = 0x44 then .day
  else if byte = 0x46 then .fok
  else if byte = 0x43 then .gtc
  else .gtd

def ofByte (byte : UInt8) : TimeInForce :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : TimeInForce) : ofByte value.toByte = value := by
  cases value with
  | ioc => decide
  | day => decide
  | fok => decide
  | gtc => decide
  | gtd => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : TimeInForce) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (TimeInForce × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : TimeInForce) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : TimeInForce) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end TimeInForce

/-- Login Status: one byte code -/
def LoginStatus.codes : List UInt8 :=
  [0x20, 0x58, 0x53, 0x4E, 0x49, 0x41, 0x4C]

inductive LoginStatus where
  | successful -- Successful
  | rejected -- Rejected
  | requestedSessionIsNotAvailable -- Requested Session Is Not Available
  | invalidStartSequenceNumberRequested -- Invalid Start Sequence Number Requested
  | incompatibleSessionProtocolVersion -- Incompatible Session Protocol Version
  | incompatibleApplicationProtocolVersion -- Incompatible Application Protocol Version
  | requestRejectedBecauseClientAlreadyLoggedIn -- Request Rejected Because Client Already Logged In
  | unlisted (byte : { byte : UInt8 // byte ∉ LoginStatus.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace LoginStatus

def toByte : LoginStatus → UInt8
  | .successful => 0x20
  | .rejected => 0x58
  | .requestedSessionIsNotAvailable => 0x53
  | .invalidStartSequenceNumberRequested => 0x4E
  | .incompatibleSessionProtocolVersion => 0x49
  | .incompatibleApplicationProtocolVersion => 0x41
  | .requestRejectedBecauseClientAlreadyLoggedIn => 0x4C
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : LoginStatus :=
  if byte = 0x20 then .successful
  else if byte = 0x58 then .rejected
  else if byte = 0x53 then .requestedSessionIsNotAvailable
  else if byte = 0x4E then .invalidStartSequenceNumberRequested
  else if byte = 0x49 then .incompatibleSessionProtocolVersion
  else if byte = 0x41 then .incompatibleApplicationProtocolVersion
  else .requestRejectedBecauseClientAlreadyLoggedIn

def ofByte (byte : UInt8) : LoginStatus :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : LoginStatus) : ofByte value.toByte = value := by
  cases value with
  | successful => decide
  | rejected => decide
  | requestedSessionIsNotAvailable => decide
  | invalidStartSequenceNumberRequested => decide
  | incompatibleSessionProtocolVersion => decide
  | incompatibleApplicationProtocolVersion => decide
  | requestRejectedBecauseClientAlreadyLoggedIn => decide
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

/-- Logout Reason: one byte code -/
def LogoutReason.codes : List UInt8 :=
  [0x20, 0x42, 0x4C, 0x41]

inductive LogoutReason where
  | gracefulLogout -- Graceful Logout
  | badPacket -- Bad Packet
  | timedOut -- Timed Out
  | applicationTerminatingConnection -- Application Terminating Connection
  | unlisted (byte : { byte : UInt8 // byte ∉ LogoutReason.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace LogoutReason

def toByte : LogoutReason → UInt8
  | .gracefulLogout => 0x20
  | .badPacket => 0x42
  | .timedOut => 0x4C
  | .applicationTerminatingConnection => 0x41
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : LogoutReason :=
  if byte = 0x20 then .gracefulLogout
  else if byte = 0x42 then .badPacket
  else if byte = 0x4C then .timedOut
  else .applicationTerminatingConnection

def ofByte (byte : UInt8) : LogoutReason :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : LogoutReason) : ofByte value.toByte = value := by
  cases value with
  | gracefulLogout => decide
  | badPacket => decide
  | timedOut => decide
  | applicationTerminatingConnection => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : LogoutReason) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (LogoutReason × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : LogoutReason) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : LogoutReason) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end LogoutReason

/-- New Order Response Message: 56 bytes -/
structure NewOrderResponseMessage where
  matchingEngine : BitVec 64
  mpId : Alpha 5
  clientOrderId : Alpha 20
  instrumentIdBinaryU4 : BitVec 32
  orderId : BitVec 64
  status : Alpha 1
  reserved10 : Alpha 10
  deriving DecidableEq, Repr

namespace NewOrderResponseMessage

def encode (message : NewOrderResponseMessage) : List UInt8 :=
  encodeUIntLE 8 message.matchingEngine
    ++ (Alpha.encode message.mpId
    ++ (Alpha.encode message.clientOrderId
    ++ (encodeUIntLE 4 message.instrumentIdBinaryU4
    ++ (encodeUIntLE 8 message.orderId
    ++ (Alpha.encode message.status
    ++ (Alpha.encode message.reserved10))))))

def decode (bytes : List UInt8) : Option (NewOrderResponseMessage × List UInt8) := do
  let (matchingEngine, bytes) ← decodeUIntLE 8 bytes
  let (mpId, bytes) ← Alpha.decode 5 bytes
  let (clientOrderId, bytes) ← Alpha.decode 20 bytes
  let (instrumentIdBinaryU4, bytes) ← decodeUIntLE 4 bytes
  let (orderId, bytes) ← decodeUIntLE 8 bytes
  let (status, bytes) ← Alpha.decode 1 bytes
  let (reserved10, bytes) ← Alpha.decode 10 bytes
  pure ({ matchingEngine, mpId, clientOrderId, instrumentIdBinaryU4, orderId, status, reserved10 }, bytes)

@[simp] theorem encode_length (message : NewOrderResponseMessage) : (encode message).length = 56 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length]

theorem encode_length_pos (message : NewOrderResponseMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : NewOrderResponseMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
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
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end NewOrderResponseMessage

/-- Modify Order Response: 80 bytes -/
structure ModifyOrderResponse where
  matchingEngineTime : BitVec 64
  mpId : Alpha 5
  clientOrderId : Alpha 20
  originalClientOrderId : Alpha 20
  instrumentIdBinaryU4 : BitVec 32
  orderId : BitVec 64
  leavesQty : BitVec 32
  status : Alpha 1
  reserved10 : Alpha 10
  deriving DecidableEq, Repr

namespace ModifyOrderResponse

def encode (message : ModifyOrderResponse) : List UInt8 :=
  encodeUIntLE 8 message.matchingEngineTime
    ++ (Alpha.encode message.mpId
    ++ (Alpha.encode message.clientOrderId
    ++ (Alpha.encode message.originalClientOrderId
    ++ (encodeUIntLE 4 message.instrumentIdBinaryU4
    ++ (encodeUIntLE 8 message.orderId
    ++ (encodeUIntLE 4 message.leavesQty
    ++ (Alpha.encode message.status
    ++ (Alpha.encode message.reserved10))))))))

def decode (bytes : List UInt8) : Option (ModifyOrderResponse × List UInt8) := do
  let (matchingEngineTime, bytes) ← decodeUIntLE 8 bytes
  let (mpId, bytes) ← Alpha.decode 5 bytes
  let (clientOrderId, bytes) ← Alpha.decode 20 bytes
  let (originalClientOrderId, bytes) ← Alpha.decode 20 bytes
  let (instrumentIdBinaryU4, bytes) ← decodeUIntLE 4 bytes
  let (orderId, bytes) ← decodeUIntLE 8 bytes
  let (leavesQty, bytes) ← decodeUIntLE 4 bytes
  let (status, bytes) ← Alpha.decode 1 bytes
  let (reserved10, bytes) ← Alpha.decode 10 bytes
  pure ({ matchingEngineTime, mpId, clientOrderId, originalClientOrderId, instrumentIdBinaryU4, orderId, leavesQty, status, reserved10 }, bytes)

@[simp] theorem encode_length (message : ModifyOrderResponse) : (encode message).length = 80 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length]

theorem encode_length_pos (message : ModifyOrderResponse) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : ModifyOrderResponse) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
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
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end ModifyOrderResponse

/-- Cancel Order Response: 66 bytes -/
structure CancelOrderResponse where
  matchingEngineTime : BitVec 64
  mpId : Alpha 5
  clientOrderId : Alpha 20
  originalClientOrder : Alpha 20
  instrumentIdBinaryU4 : BitVec 32
  orderId : BitVec 64
  status : Alpha 1
  deriving DecidableEq, Repr

namespace CancelOrderResponse

def encode (message : CancelOrderResponse) : List UInt8 :=
  encodeUIntLE 8 message.matchingEngineTime
    ++ (Alpha.encode message.mpId
    ++ (Alpha.encode message.clientOrderId
    ++ (Alpha.encode message.originalClientOrder
    ++ (encodeUIntLE 4 message.instrumentIdBinaryU4
    ++ (encodeUIntLE 8 message.orderId
    ++ (Alpha.encode message.status))))))

def decode (bytes : List UInt8) : Option (CancelOrderResponse × List UInt8) := do
  let (matchingEngineTime, bytes) ← decodeUIntLE 8 bytes
  let (mpId, bytes) ← Alpha.decode 5 bytes
  let (clientOrderId, bytes) ← Alpha.decode 20 bytes
  let (originalClientOrder, bytes) ← Alpha.decode 20 bytes
  let (instrumentIdBinaryU4, bytes) ← decodeUIntLE 4 bytes
  let (orderId, bytes) ← decodeUIntLE 8 bytes
  let (status, bytes) ← Alpha.decode 1 bytes
  pure ({ matchingEngineTime, mpId, clientOrderId, originalClientOrder, instrumentIdBinaryU4, orderId, status }, bytes)

@[simp] theorem encode_length (message : CancelOrderResponse) : (encode message).length = 66 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length]

theorem encode_length_pos (message : CancelOrderResponse) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : CancelOrderResponse) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
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

end CancelOrderResponse

/-- Mass Cancel Response: 44 bytes -/
structure MassCancelResponse where
  matchingEngineTime : BitVec 64
  mpId : Alpha 5
  clientOrderId : Alpha 20
  status : Alpha 1
  reserved10 : Alpha 10
  deriving DecidableEq, Repr

namespace MassCancelResponse

def encode (message : MassCancelResponse) : List UInt8 :=
  encodeUIntLE 8 message.matchingEngineTime
    ++ (Alpha.encode message.mpId
    ++ (Alpha.encode message.clientOrderId
    ++ (Alpha.encode message.status
    ++ (Alpha.encode message.reserved10))))

def decode (bytes : List UInt8) : Option (MassCancelResponse × List UInt8) := do
  let (matchingEngineTime, bytes) ← decodeUIntLE 8 bytes
  let (mpId, bytes) ← Alpha.decode 5 bytes
  let (clientOrderId, bytes) ← Alpha.decode 20 bytes
  let (status, bytes) ← Alpha.decode 1 bytes
  let (reserved10, bytes) ← Alpha.decode 10 bytes
  pure ({ matchingEngineTime, mpId, clientOrderId, status, reserved10 }, bytes)

@[simp] theorem encode_length (message : MassCancelResponse) : (encode message).length = 44 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length]

theorem encode_length_pos (message : MassCancelResponse) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : MassCancelResponse) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end MassCancelResponse

/-- Strategy Creation Response Message: 70 bytes -/
structure StrategyCreationResponseMessage where
  matchingEngineTime : BitVec 64
  mpId : Alpha 5
  clientOrderId : Alpha 20
  instrumentIdString20 : Alpha 20
  status : Alpha 1
  reserved16 : Alpha 16
  deriving DecidableEq, Repr

namespace StrategyCreationResponseMessage

def encode (message : StrategyCreationResponseMessage) : List UInt8 :=
  encodeUIntLE 8 message.matchingEngineTime
    ++ (Alpha.encode message.mpId
    ++ (Alpha.encode message.clientOrderId
    ++ (Alpha.encode message.instrumentIdString20
    ++ (Alpha.encode message.status
    ++ (Alpha.encode message.reserved16)))))

def decode (bytes : List UInt8) : Option (StrategyCreationResponseMessage × List UInt8) := do
  let (matchingEngineTime, bytes) ← decodeUIntLE 8 bytes
  let (mpId, bytes) ← Alpha.decode 5 bytes
  let (clientOrderId, bytes) ← Alpha.decode 20 bytes
  let (instrumentIdString20, bytes) ← Alpha.decode 20 bytes
  let (status, bytes) ← Alpha.decode 1 bytes
  let (reserved16, bytes) ← Alpha.decode 16 bytes
  pure ({ matchingEngineTime, mpId, clientOrderId, instrumentIdString20, status, reserved16 }, bytes)

@[simp] theorem encode_length (message : StrategyCreationResponseMessage) : (encode message).length = 70 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length]

theorem encode_length_pos (message : StrategyCreationResponseMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : StrategyCreationResponseMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end StrategyCreationResponseMessage

/-- System State Notification Message: 26 bytes -/
structure SystemStateNotificationMessage where
  matchingEngineTime : BitVec 64
  version : Alpha 8
  sessionId : BitVec 8
  systemStatus : Alpha 1
  reserved8 : Alpha 8
  deriving DecidableEq, Repr

namespace SystemStateNotificationMessage

def encode (message : SystemStateNotificationMessage) : List UInt8 :=
  encodeUIntLE 8 message.matchingEngineTime
    ++ (Alpha.encode message.version
    ++ (encodeUIntLE 1 message.sessionId
    ++ (Alpha.encode message.systemStatus
    ++ (Alpha.encode message.reserved8))))

def decode (bytes : List UInt8) : Option (SystemStateNotificationMessage × List UInt8) := do
  let (matchingEngineTime, bytes) ← decodeUIntLE 8 bytes
  let (version, bytes) ← Alpha.decode 8 bytes
  let (sessionId, bytes) ← decodeUIntLE 1 bytes
  let (systemStatus, bytes) ← Alpha.decode 1 bytes
  let (reserved8, bytes) ← Alpha.decode 8 bytes
  pure ({ matchingEngineTime, version, sessionId, systemStatus, reserved8 }, bytes)

@[simp] theorem encode_length (message : SystemStateNotificationMessage) : (encode message).length = 26 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length]

theorem encode_length_pos (message : SystemStateNotificationMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SystemStateNotificationMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
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

end SystemStateNotificationMessage

/-- New Order Notification: 190 bytes -/
structure NewOrderNotification where
  matchingEngineTime : BitVec 64
  mpId : Alpha 5
  orderId : BitVec 64
  clientSendTime : BitVec 64
  operatorId : Alpha 18
  operatorLocation : Alpha 6
  account : Alpha 16
  clientOrderId : Alpha 20
  instrumentIdBinaryU4 : BitVec 32
  price : BitVec 64
  stopOrderTriggerPrice : BitVec 64
  sizeBinaryU4 : BitVec 32
  orderInstructions : BitVec 16
  timeInForce : TimeInForce
  orderType : Alpha 1
  selfTradeProtection : BitVec 8
  selfTradeProtectionGroup : Alpha 2
  purgeGroup : Alpha 1
  customerOrderHandlingInstruction : Alpha 1
  additionalOrderIndicators : BitVec 8
  minQty : BitVec 32
  orderExpiryDate : BitVec 16
  tradingCollarDollarValue : BitVec 64
  ctiCode : Alpha 1
  textMemo : Alpha 20
  reserved32 : Alpha 32
  deriving DecidableEq, Repr

namespace NewOrderNotification

def encode (message : NewOrderNotification) : List UInt8 :=
  encodeUIntLE 8 message.matchingEngineTime
    ++ (Alpha.encode message.mpId
    ++ (encodeUIntLE 8 message.orderId
    ++ (encodeUIntLE 8 message.clientSendTime
    ++ (Alpha.encode message.operatorId
    ++ (Alpha.encode message.operatorLocation
    ++ (Alpha.encode message.account
    ++ (Alpha.encode message.clientOrderId
    ++ (encodeUIntLE 4 message.instrumentIdBinaryU4
    ++ (encodeUIntLE 8 message.price
    ++ (encodeUIntLE 8 message.stopOrderTriggerPrice
    ++ (encodeUIntLE 4 message.sizeBinaryU4
    ++ (encodeUIntLE 2 message.orderInstructions
    ++ (TimeInForce.encode message.timeInForce
    ++ (Alpha.encode message.orderType
    ++ (encodeUIntLE 1 message.selfTradeProtection
    ++ (Alpha.encode message.selfTradeProtectionGroup
    ++ (Alpha.encode message.purgeGroup
    ++ (Alpha.encode message.customerOrderHandlingInstruction
    ++ (encodeUIntLE 1 message.additionalOrderIndicators
    ++ (encodeUIntLE 4 message.minQty
    ++ (encodeUIntLE 2 message.orderExpiryDate
    ++ (encodeUIntLE 8 message.tradingCollarDollarValue
    ++ (Alpha.encode message.ctiCode
    ++ (Alpha.encode message.textMemo
    ++ (Alpha.encode message.reserved32)))))))))))))))))))))))))

-- a long run of fields nests deeper than the elaborator's default limit
set_option maxRecDepth 4096 in
def decode (bytes : List UInt8) : Option (NewOrderNotification × List UInt8) := do
  let (matchingEngineTime, bytes) ← decodeUIntLE 8 bytes
  let (mpId, bytes) ← Alpha.decode 5 bytes
  let (orderId, bytes) ← decodeUIntLE 8 bytes
  let (clientSendTime, bytes) ← decodeUIntLE 8 bytes
  let (operatorId, bytes) ← Alpha.decode 18 bytes
  let (operatorLocation, bytes) ← Alpha.decode 6 bytes
  let (account, bytes) ← Alpha.decode 16 bytes
  let (clientOrderId, bytes) ← Alpha.decode 20 bytes
  let (instrumentIdBinaryU4, bytes) ← decodeUIntLE 4 bytes
  let (price, bytes) ← decodeUIntLE 8 bytes
  let (stopOrderTriggerPrice, bytes) ← decodeUIntLE 8 bytes
  let (sizeBinaryU4, bytes) ← decodeUIntLE 4 bytes
  let (orderInstructions, bytes) ← decodeUIntLE 2 bytes
  let (timeInForce, bytes) ← TimeInForce.decode bytes
  let (orderType, bytes) ← Alpha.decode 1 bytes
  let (selfTradeProtection, bytes) ← decodeUIntLE 1 bytes
  let (selfTradeProtectionGroup, bytes) ← Alpha.decode 2 bytes
  let (purgeGroup, bytes) ← Alpha.decode 1 bytes
  let (customerOrderHandlingInstruction, bytes) ← Alpha.decode 1 bytes
  let (additionalOrderIndicators, bytes) ← decodeUIntLE 1 bytes
  let (minQty, bytes) ← decodeUIntLE 4 bytes
  let (orderExpiryDate, bytes) ← decodeUIntLE 2 bytes
  let (tradingCollarDollarValue, bytes) ← decodeUIntLE 8 bytes
  let (ctiCode, bytes) ← Alpha.decode 1 bytes
  let (textMemo, bytes) ← Alpha.decode 20 bytes
  let (reserved32, bytes) ← Alpha.decode 32 bytes
  pure ({ matchingEngineTime, mpId, orderId, clientSendTime, operatorId, operatorLocation, account, clientOrderId, instrumentIdBinaryU4, price, stopOrderTriggerPrice, sizeBinaryU4, orderInstructions, timeInForce, orderType, selfTradeProtection, selfTradeProtectionGroup, purgeGroup, customerOrderHandlingInstruction, additionalOrderIndicators, minQty, orderExpiryDate, tradingCollarDollarValue, ctiCode, textMemo, reserved32 }, bytes)

@[simp] theorem encode_length (message : NewOrderNotification) : (encode message).length = 190 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length, TimeInForce.encode_length]

theorem encode_length_pos (message : NewOrderNotification) : (encode message).length > 0 := by
  rw [encode_length]
  decide

set_option maxRecDepth 4096 in
@[simp] theorem decode_encode (message : NewOrderNotification) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
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
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
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
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, TimeInForce.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
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
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end NewOrderNotification

/-- Modify Order Notification: 160 bytes -/
structure ModifyOrderNotification where
  matchingEngineTime : BitVec 64
  mpId : Alpha 5
  orderId : BitVec 64
  clientSendTime : BitVec 64
  leavesQty : BitVec 32
  operatorId : Alpha 18
  operatorLocation : Alpha 6
  clientOrderId : Alpha 20
  originalClientOrderId : Alpha 20
  instrumentIdBinaryU4 : BitVec 32
  price : BitVec 64
  stopOrderTriggerPrice : BitVec 64
  sizeBinaryS4 : BitVec 32
  orderExpiryDate : BitVec 16
  selfTradeProtectionGroup : Alpha 2
  purgeGroup : Alpha 1
  customerOrderHandlingInstruction : Alpha 1
  additionalOrderIndicators : BitVec 8
  reserved32 : Alpha 32
  deriving DecidableEq, Repr

namespace ModifyOrderNotification

def encode (message : ModifyOrderNotification) : List UInt8 :=
  encodeUIntLE 8 message.matchingEngineTime
    ++ (Alpha.encode message.mpId
    ++ (encodeUIntLE 8 message.orderId
    ++ (encodeUIntLE 8 message.clientSendTime
    ++ (encodeUIntLE 4 message.leavesQty
    ++ (Alpha.encode message.operatorId
    ++ (Alpha.encode message.operatorLocation
    ++ (Alpha.encode message.clientOrderId
    ++ (Alpha.encode message.originalClientOrderId
    ++ (encodeUIntLE 4 message.instrumentIdBinaryU4
    ++ (encodeUIntLE 8 message.price
    ++ (encodeUIntLE 8 message.stopOrderTriggerPrice
    ++ (encodeUIntLE 4 message.sizeBinaryS4
    ++ (encodeUIntLE 2 message.orderExpiryDate
    ++ (Alpha.encode message.selfTradeProtectionGroup
    ++ (Alpha.encode message.purgeGroup
    ++ (Alpha.encode message.customerOrderHandlingInstruction
    ++ (encodeUIntLE 1 message.additionalOrderIndicators
    ++ (Alpha.encode message.reserved32))))))))))))))))))

def decode (bytes : List UInt8) : Option (ModifyOrderNotification × List UInt8) := do
  let (matchingEngineTime, bytes) ← decodeUIntLE 8 bytes
  let (mpId, bytes) ← Alpha.decode 5 bytes
  let (orderId, bytes) ← decodeUIntLE 8 bytes
  let (clientSendTime, bytes) ← decodeUIntLE 8 bytes
  let (leavesQty, bytes) ← decodeUIntLE 4 bytes
  let (operatorId, bytes) ← Alpha.decode 18 bytes
  let (operatorLocation, bytes) ← Alpha.decode 6 bytes
  let (clientOrderId, bytes) ← Alpha.decode 20 bytes
  let (originalClientOrderId, bytes) ← Alpha.decode 20 bytes
  let (instrumentIdBinaryU4, bytes) ← decodeUIntLE 4 bytes
  let (price, bytes) ← decodeUIntLE 8 bytes
  let (stopOrderTriggerPrice, bytes) ← decodeUIntLE 8 bytes
  let (sizeBinaryS4, bytes) ← decodeUIntLE 4 bytes
  let (orderExpiryDate, bytes) ← decodeUIntLE 2 bytes
  let (selfTradeProtectionGroup, bytes) ← Alpha.decode 2 bytes
  let (purgeGroup, bytes) ← Alpha.decode 1 bytes
  let (customerOrderHandlingInstruction, bytes) ← Alpha.decode 1 bytes
  let (additionalOrderIndicators, bytes) ← decodeUIntLE 1 bytes
  let (reserved32, bytes) ← Alpha.decode 32 bytes
  pure ({ matchingEngineTime, mpId, orderId, clientSendTime, leavesQty, operatorId, operatorLocation, clientOrderId, originalClientOrderId, instrumentIdBinaryU4, price, stopOrderTriggerPrice, sizeBinaryS4, orderExpiryDate, selfTradeProtectionGroup, purgeGroup, customerOrderHandlingInstruction, additionalOrderIndicators, reserved32 }, bytes)

@[simp] theorem encode_length (message : ModifyOrderNotification) : (encode message).length = 160 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length]

theorem encode_length_pos (message : ModifyOrderNotification) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : ModifyOrderNotification) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
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
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end ModifyOrderNotification

/-- Cancel Reduce Size Order Notification: 102 bytes -/
structure CancelReduceSizeOrderNotification where
  matchingEngineTime : BitVec 64
  mpId : Alpha 5
  operatorId : Alpha 18
  operatorLocation : Alpha 6
  clientOrderId : Alpha 20
  instrumentIdBinaryU4 : BitVec 32
  orderId : BitVec 64
  clientSendTime : BitVec 64
  leavesQty : BitVec 32
  cancelReason : Alpha 1
  lastPrice : BitVec 64
  lastSize : BitVec 32
  reserved8 : Alpha 8
  deriving DecidableEq, Repr

namespace CancelReduceSizeOrderNotification

def encode (message : CancelReduceSizeOrderNotification) : List UInt8 :=
  encodeUIntLE 8 message.matchingEngineTime
    ++ (Alpha.encode message.mpId
    ++ (Alpha.encode message.operatorId
    ++ (Alpha.encode message.operatorLocation
    ++ (Alpha.encode message.clientOrderId
    ++ (encodeUIntLE 4 message.instrumentIdBinaryU4
    ++ (encodeUIntLE 8 message.orderId
    ++ (encodeUIntLE 8 message.clientSendTime
    ++ (encodeUIntLE 4 message.leavesQty
    ++ (Alpha.encode message.cancelReason
    ++ (encodeUIntLE 8 message.lastPrice
    ++ (encodeUIntLE 4 message.lastSize
    ++ (Alpha.encode message.reserved8))))))))))))

def decode (bytes : List UInt8) : Option (CancelReduceSizeOrderNotification × List UInt8) := do
  let (matchingEngineTime, bytes) ← decodeUIntLE 8 bytes
  let (mpId, bytes) ← Alpha.decode 5 bytes
  let (operatorId, bytes) ← Alpha.decode 18 bytes
  let (operatorLocation, bytes) ← Alpha.decode 6 bytes
  let (clientOrderId, bytes) ← Alpha.decode 20 bytes
  let (instrumentIdBinaryU4, bytes) ← decodeUIntLE 4 bytes
  let (orderId, bytes) ← decodeUIntLE 8 bytes
  let (clientSendTime, bytes) ← decodeUIntLE 8 bytes
  let (leavesQty, bytes) ← decodeUIntLE 4 bytes
  let (cancelReason, bytes) ← Alpha.decode 1 bytes
  let (lastPrice, bytes) ← decodeUIntLE 8 bytes
  let (lastSize, bytes) ← decodeUIntLE 4 bytes
  let (reserved8, bytes) ← Alpha.decode 8 bytes
  pure ({ matchingEngineTime, mpId, operatorId, operatorLocation, clientOrderId, instrumentIdBinaryU4, orderId, clientSendTime, leavesQty, cancelReason, lastPrice, lastSize, reserved8 }, bytes)

@[simp] theorem encode_length (message : CancelReduceSizeOrderNotification) : (encode message).length = 102 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length]

theorem encode_length_pos (message : CancelReduceSizeOrderNotification) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : CancelReduceSizeOrderNotification) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
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
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end CancelReduceSizeOrderNotification

/-- Order Status Update Notification: 53 bytes -/
structure OrderStatusUpdateNotification where
  matchingEngineTime : BitVec 64
  instrumentIdBinaryU4 : BitVec 32
  orderId : BitVec 64
  updateStatus : Alpha 1
  reserved32 : Alpha 32
  deriving DecidableEq, Repr

namespace OrderStatusUpdateNotification

def encode (message : OrderStatusUpdateNotification) : List UInt8 :=
  encodeUIntLE 8 message.matchingEngineTime
    ++ (encodeUIntLE 4 message.instrumentIdBinaryU4
    ++ (encodeUIntLE 8 message.orderId
    ++ (Alpha.encode message.updateStatus
    ++ (Alpha.encode message.reserved32))))

def decode (bytes : List UInt8) : Option (OrderStatusUpdateNotification × List UInt8) := do
  let (matchingEngineTime, bytes) ← decodeUIntLE 8 bytes
  let (instrumentIdBinaryU4, bytes) ← decodeUIntLE 4 bytes
  let (orderId, bytes) ← decodeUIntLE 8 bytes
  let (updateStatus, bytes) ← Alpha.decode 1 bytes
  let (reserved32, bytes) ← Alpha.decode 32 bytes
  pure ({ matchingEngineTime, instrumentIdBinaryU4, orderId, updateStatus, reserved32 }, bytes)

@[simp] theorem encode_length (message : OrderStatusUpdateNotification) : (encode message).length = 53 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length]

theorem encode_length_pos (message : OrderStatusUpdateNotification) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OrderStatusUpdateNotification) (rest : List UInt8) :
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
  rw [Alpha.decode_encode, some_bind]
  rfl

end OrderStatusUpdateNotification

/-- Simple Execution Notification: 159 bytes -/
structure SimpleExecutionNotification where
  matchingEngineTime : BitVec 64
  mpId : Alpha 5
  operatorId : Alpha 18
  operatorLocation : Alpha 6
  instrumentIdBinaryU4 : BitVec 32
  clientOrderId : Alpha 20
  simpleTradeId : BitVec 64
  complexTradeId : BitVec 64
  executionId : BitVec 64
  tradeDate : BitVec 16
  correctionNumber : BitVec 8
  tradeStatus : Alpha 1
  lastPrice : BitVec 64
  lastSize : BitVec 32
  orderInstructions : BitVec 16
  ctiCode : Alpha 1
  textMemo : Alpha 20
  liquidityIndicator : Alpha 3
  reserved32 : Alpha 32
  deriving DecidableEq, Repr

namespace SimpleExecutionNotification

def encode (message : SimpleExecutionNotification) : List UInt8 :=
  encodeUIntLE 8 message.matchingEngineTime
    ++ (Alpha.encode message.mpId
    ++ (Alpha.encode message.operatorId
    ++ (Alpha.encode message.operatorLocation
    ++ (encodeUIntLE 4 message.instrumentIdBinaryU4
    ++ (Alpha.encode message.clientOrderId
    ++ (encodeUIntLE 8 message.simpleTradeId
    ++ (encodeUIntLE 8 message.complexTradeId
    ++ (encodeUIntLE 8 message.executionId
    ++ (encodeUIntLE 2 message.tradeDate
    ++ (encodeUIntLE 1 message.correctionNumber
    ++ (Alpha.encode message.tradeStatus
    ++ (encodeUIntLE 8 message.lastPrice
    ++ (encodeUIntLE 4 message.lastSize
    ++ (encodeUIntLE 2 message.orderInstructions
    ++ (Alpha.encode message.ctiCode
    ++ (Alpha.encode message.textMemo
    ++ (Alpha.encode message.liquidityIndicator
    ++ (Alpha.encode message.reserved32))))))))))))))))))

def decode (bytes : List UInt8) : Option (SimpleExecutionNotification × List UInt8) := do
  let (matchingEngineTime, bytes) ← decodeUIntLE 8 bytes
  let (mpId, bytes) ← Alpha.decode 5 bytes
  let (operatorId, bytes) ← Alpha.decode 18 bytes
  let (operatorLocation, bytes) ← Alpha.decode 6 bytes
  let (instrumentIdBinaryU4, bytes) ← decodeUIntLE 4 bytes
  let (clientOrderId, bytes) ← Alpha.decode 20 bytes
  let (simpleTradeId, bytes) ← decodeUIntLE 8 bytes
  let (complexTradeId, bytes) ← decodeUIntLE 8 bytes
  let (executionId, bytes) ← decodeUIntLE 8 bytes
  let (tradeDate, bytes) ← decodeUIntLE 2 bytes
  let (correctionNumber, bytes) ← decodeUIntLE 1 bytes
  let (tradeStatus, bytes) ← Alpha.decode 1 bytes
  let (lastPrice, bytes) ← decodeUIntLE 8 bytes
  let (lastSize, bytes) ← decodeUIntLE 4 bytes
  let (orderInstructions, bytes) ← decodeUIntLE 2 bytes
  let (ctiCode, bytes) ← Alpha.decode 1 bytes
  let (textMemo, bytes) ← Alpha.decode 20 bytes
  let (liquidityIndicator, bytes) ← Alpha.decode 3 bytes
  let (reserved32, bytes) ← Alpha.decode 32 bytes
  pure ({ matchingEngineTime, mpId, operatorId, operatorLocation, instrumentIdBinaryU4, clientOrderId, simpleTradeId, complexTradeId, executionId, tradeDate, correctionNumber, tradeStatus, lastPrice, lastSize, orderInstructions, ctiCode, textMemo, liquidityIndicator, reserved32 }, bytes)

@[simp] theorem encode_length (message : SimpleExecutionNotification) : (encode message).length = 159 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length]

theorem encode_length_pos (message : SimpleExecutionNotification) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SimpleExecutionNotification) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
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
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end SimpleExecutionNotification

/-- Complex Execution Notification: 93 bytes -/
structure ComplexExecutionNotification where
  matchingEngineTime : BitVec 64
  mpId : Alpha 5
  instrumentIdBinaryU4 : BitVec 32
  clientOrderId : Alpha 20
  complexTradeId : BitVec 64
  tradeDate : BitVec 16
  lastNetPrice : BitVec 64
  lastSize : BitVec 32
  orderInstructions : BitVec 16
  reserved32 : Alpha 32
  deriving DecidableEq, Repr

namespace ComplexExecutionNotification

def encode (message : ComplexExecutionNotification) : List UInt8 :=
  encodeUIntLE 8 message.matchingEngineTime
    ++ (Alpha.encode message.mpId
    ++ (encodeUIntLE 4 message.instrumentIdBinaryU4
    ++ (Alpha.encode message.clientOrderId
    ++ (encodeUIntLE 8 message.complexTradeId
    ++ (encodeUIntLE 2 message.tradeDate
    ++ (encodeUIntLE 8 message.lastNetPrice
    ++ (encodeUIntLE 4 message.lastSize
    ++ (encodeUIntLE 2 message.orderInstructions
    ++ (Alpha.encode message.reserved32)))))))))

def decode (bytes : List UInt8) : Option (ComplexExecutionNotification × List UInt8) := do
  let (matchingEngineTime, bytes) ← decodeUIntLE 8 bytes
  let (mpId, bytes) ← Alpha.decode 5 bytes
  let (instrumentIdBinaryU4, bytes) ← decodeUIntLE 4 bytes
  let (clientOrderId, bytes) ← Alpha.decode 20 bytes
  let (complexTradeId, bytes) ← decodeUIntLE 8 bytes
  let (tradeDate, bytes) ← decodeUIntLE 2 bytes
  let (lastNetPrice, bytes) ← decodeUIntLE 8 bytes
  let (lastSize, bytes) ← decodeUIntLE 4 bytes
  let (orderInstructions, bytes) ← decodeUIntLE 2 bytes
  let (reserved32, bytes) ← Alpha.decode 32 bytes
  pure ({ matchingEngineTime, mpId, instrumentIdBinaryU4, clientOrderId, complexTradeId, tradeDate, lastNetPrice, lastSize, orderInstructions, reserved32 }, bytes)

@[simp] theorem encode_length (message : ComplexExecutionNotification) : (encode message).length = 93 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length]

theorem encode_length_pos (message : ComplexExecutionNotification) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : ComplexExecutionNotification) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
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
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end ComplexExecutionNotification

/-- Any Sequenced Message, selected by Sequenced Message Type -/
inductive SequencedMessage where
  | newOrderResponseMessage (message : NewOrderResponseMessage) -- "NR" 0x4E52
  | modifyOrderResponse (message : ModifyOrderResponse) -- "MR" 0x4D52
  | cancelOrderResponse (message : CancelOrderResponse) -- "CR" 0x4352
  | massCancelResponse (message : MassCancelResponse) -- "XR" 0x5852
  | strategyCreationResponseMessage (message : StrategyCreationResponseMessage) -- "SR" 0x5352
  | systemStateNotificationMessage (message : SystemStateNotificationMessage) -- "SN" 0x534E
  | newOrderNotification (message : NewOrderNotification) -- "O1" 0x4F31
  | modifyOrderNotification (message : ModifyOrderNotification) -- "MN" 0x4D4E
  | cancelReduceSizeOrderNotification (message : CancelReduceSizeOrderNotification) -- "XN" 0x584E
  | orderStatusUpdateNotification (message : OrderStatusUpdateNotification) -- "OS" 0x4F53
  | simpleExecutionNotification (message : SimpleExecutionNotification) -- "EN" 0x454E
  | complexExecutionNotification (message : ComplexExecutionNotification) -- "CN" 0x434E
  deriving DecidableEq, Repr

namespace SequencedMessage

/-- The Sequenced Message Type each message is sent under -/
def tag : SequencedMessage → BitVec 16
  | .newOrderResponseMessage _ => 20050
  | .modifyOrderResponse _ => 19794
  | .cancelOrderResponse _ => 17234
  | .massCancelResponse _ => 22610
  | .strategyCreationResponseMessage _ => 21330
  | .systemStateNotificationMessage _ => 21326
  | .newOrderNotification _ => 20273
  | .modifyOrderNotification _ => 19790
  | .cancelReduceSizeOrderNotification _ => 22606
  | .orderStatusUpdateNotification _ => 20307
  | .simpleExecutionNotification _ => 17742
  | .complexExecutionNotification _ => 17230

def encode : SequencedMessage → List UInt8
  | .newOrderResponseMessage message => NewOrderResponseMessage.encode message
  | .modifyOrderResponse message => ModifyOrderResponse.encode message
  | .cancelOrderResponse message => CancelOrderResponse.encode message
  | .massCancelResponse message => MassCancelResponse.encode message
  | .strategyCreationResponseMessage message => StrategyCreationResponseMessage.encode message
  | .systemStateNotificationMessage message => SystemStateNotificationMessage.encode message
  | .newOrderNotification message => NewOrderNotification.encode message
  | .modifyOrderNotification message => ModifyOrderNotification.encode message
  | .cancelReduceSizeOrderNotification message => CancelReduceSizeOrderNotification.encode message
  | .orderStatusUpdateNotification message => OrderStatusUpdateNotification.encode message
  | .simpleExecutionNotification message => SimpleExecutionNotification.encode message
  | .complexExecutionNotification message => ComplexExecutionNotification.encode message

/-- The most bytes any message's encoding can take -/
theorem encode_length_le (message : SequencedMessage) : (encode message).length ≤ 190 := by
  cases message with
  | newOrderResponseMessage inner =>
    simp only [encode, NewOrderResponseMessage.encode_length]
    omega
  | modifyOrderResponse inner =>
    simp only [encode, ModifyOrderResponse.encode_length]
    omega
  | cancelOrderResponse inner =>
    simp only [encode, CancelOrderResponse.encode_length]
    omega
  | massCancelResponse inner =>
    simp only [encode, MassCancelResponse.encode_length]
    omega
  | strategyCreationResponseMessage inner =>
    simp only [encode, StrategyCreationResponseMessage.encode_length]
    omega
  | systemStateNotificationMessage inner =>
    simp only [encode, SystemStateNotificationMessage.encode_length]
    omega
  | newOrderNotification inner =>
    simp only [encode, NewOrderNotification.encode_length]
    omega
  | modifyOrderNotification inner =>
    simp only [encode, ModifyOrderNotification.encode_length]
    omega
  | cancelReduceSizeOrderNotification inner =>
    simp only [encode, CancelReduceSizeOrderNotification.encode_length]
    omega
  | orderStatusUpdateNotification inner =>
    simp only [encode, OrderStatusUpdateNotification.encode_length]
    omega
  | simpleExecutionNotification inner =>
    simp only [encode, SimpleExecutionNotification.encode_length]
    omega
  | complexExecutionNotification inner =>
    simp only [encode, ComplexExecutionNotification.encode_length]
    omega

def decode (tag : BitVec 16) (bytes : List UInt8) : Option (SequencedMessage × List UInt8) :=
  if tag = 20050 then (NewOrderResponseMessage.decode bytes).map fun (message, rest) => (.newOrderResponseMessage message, rest)
  else if tag = 19794 then (ModifyOrderResponse.decode bytes).map fun (message, rest) => (.modifyOrderResponse message, rest)
  else if tag = 17234 then (CancelOrderResponse.decode bytes).map fun (message, rest) => (.cancelOrderResponse message, rest)
  else if tag = 22610 then (MassCancelResponse.decode bytes).map fun (message, rest) => (.massCancelResponse message, rest)
  else if tag = 21330 then (StrategyCreationResponseMessage.decode bytes).map fun (message, rest) => (.strategyCreationResponseMessage message, rest)
  else if tag = 21326 then (SystemStateNotificationMessage.decode bytes).map fun (message, rest) => (.systemStateNotificationMessage message, rest)
  else if tag = 20273 then (NewOrderNotification.decode bytes).map fun (message, rest) => (.newOrderNotification message, rest)
  else if tag = 19790 then (ModifyOrderNotification.decode bytes).map fun (message, rest) => (.modifyOrderNotification message, rest)
  else if tag = 22606 then (CancelReduceSizeOrderNotification.decode bytes).map fun (message, rest) => (.cancelReduceSizeOrderNotification message, rest)
  else if tag = 20307 then (OrderStatusUpdateNotification.decode bytes).map fun (message, rest) => (.orderStatusUpdateNotification message, rest)
  else if tag = 17742 then (SimpleExecutionNotification.decode bytes).map fun (message, rest) => (.simpleExecutionNotification message, rest)
  else if tag = 17230 then (ComplexExecutionNotification.decode bytes).map fun (message, rest) => (.complexExecutionNotification message, rest)
  else none

@[simp] theorem decode_encode (message : SequencedMessage) (rest : List UInt8) :
    decode (tag message) (encode message ++ rest) = some (message, rest) := by
  cases message <;> simp [decode, encode, tag]

end SequencedMessage

/-- Sequenced Data Packet -/
structure SequencedDataPacket where
  sequenceNumber : BitVec 64
  sequencedMessage : SequencedMessage
  deriving DecidableEq, Repr

namespace SequencedDataPacket

def encode (message : SequencedDataPacket) : List UInt8 :=
  encodeUIntLE 8 message.sequenceNumber
    ++ (encodeUInt 2 (SequencedMessage.tag message.sequencedMessage)
    ++ (SequencedMessage.encode message.sequencedMessage))

def decode (bytes : List UInt8) : Option (SequencedDataPacket × List UInt8) := do
  let (sequenceNumber, bytes) ← decodeUIntLE 8 bytes
  let (sequencedMessageType, bytes) ← decodeUInt 2 bytes
  let (sequencedMessage, bytes) ← SequencedMessage.decode sequencedMessageType bytes
  pure ({ sequenceNumber, sequencedMessage }, bytes)

theorem encode_length_pos (message : SequencedDataPacket) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUIntLE_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : SequencedDataPacket) : (encode message).length ≤ 200 := by
  unfold encode
  cases message.sequencedMessage with
  | newOrderResponseMessage inner =>
    simp only [SequencedMessage.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, encodeUInt_length, NewOrderResponseMessage.encode_length]
    omega
  | modifyOrderResponse inner =>
    simp only [SequencedMessage.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, encodeUInt_length, ModifyOrderResponse.encode_length]
    omega
  | cancelOrderResponse inner =>
    simp only [SequencedMessage.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, encodeUInt_length, CancelOrderResponse.encode_length]
    omega
  | massCancelResponse inner =>
    simp only [SequencedMessage.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, encodeUInt_length, MassCancelResponse.encode_length]
    omega
  | strategyCreationResponseMessage inner =>
    simp only [SequencedMessage.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, encodeUInt_length, StrategyCreationResponseMessage.encode_length]
    omega
  | systemStateNotificationMessage inner =>
    simp only [SequencedMessage.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, encodeUInt_length, SystemStateNotificationMessage.encode_length]
    omega
  | newOrderNotification inner =>
    simp only [SequencedMessage.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, encodeUInt_length, NewOrderNotification.encode_length]
    omega
  | modifyOrderNotification inner =>
    simp only [SequencedMessage.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, encodeUInt_length, ModifyOrderNotification.encode_length]
    omega
  | cancelReduceSizeOrderNotification inner =>
    simp only [SequencedMessage.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, encodeUInt_length, CancelReduceSizeOrderNotification.encode_length]
    omega
  | orderStatusUpdateNotification inner =>
    simp only [SequencedMessage.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, encodeUInt_length, OrderStatusUpdateNotification.encode_length]
    omega
  | simpleExecutionNotification inner =>
    simp only [SequencedMessage.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, encodeUInt_length, SimpleExecutionNotification.encode_length]
    omega
  | complexExecutionNotification inner =>
    simp only [SequencedMessage.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, encodeUInt_length, ComplexExecutionNotification.encode_length]
    omega

@[simp] theorem decode_encode (message : SequencedDataPacket) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [SequencedMessage.decode_encode, some_bind]
  rfl

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : SequencedDataPacket) : decode (encode message) = some (message, []) :=
  List.append_nil (encode message) ▸ decode_encode message []

end SequencedDataPacket

/-- New Order Request Message: 174 bytes -/
structure NewOrderRequestMessage where
  clientSendTime : BitVec 64
  mpId : Alpha 5
  operatorId : Alpha 18
  operatorLocation : Alpha 6
  account : Alpha 16
  clientOrderId : Alpha 20
  instrumentIdBinaryU4 : BitVec 32
  price : BitVec 64
  stopOrderTriggerPrice : BitVec 64
  sizeBinaryU4 : BitVec 32
  orderInstructions : BitVec 16
  timeInForce : TimeInForce
  orderType : Alpha 1
  selfTradeProtection : BitVec 8
  selfTradeProtectionGroup : Alpha 2
  purgeGroup : Alpha 1
  customerOrderHandlingInstruction : Alpha 1
  additionalOrderIndicators : BitVec 8
  minQty : BitVec 32
  orderExpiryDate : BitVec 16
  tradingCollarDollarValue : BitVec 64
  ctiCode : Alpha 1
  textMemo : Alpha 20
  reserved32 : Alpha 32
  deriving DecidableEq, Repr

namespace NewOrderRequestMessage

def encode (message : NewOrderRequestMessage) : List UInt8 :=
  encodeUIntLE 8 message.clientSendTime
    ++ (Alpha.encode message.mpId
    ++ (Alpha.encode message.operatorId
    ++ (Alpha.encode message.operatorLocation
    ++ (Alpha.encode message.account
    ++ (Alpha.encode message.clientOrderId
    ++ (encodeUIntLE 4 message.instrumentIdBinaryU4
    ++ (encodeUIntLE 8 message.price
    ++ (encodeUIntLE 8 message.stopOrderTriggerPrice
    ++ (encodeUIntLE 4 message.sizeBinaryU4
    ++ (encodeUIntLE 2 message.orderInstructions
    ++ (TimeInForce.encode message.timeInForce
    ++ (Alpha.encode message.orderType
    ++ (encodeUIntLE 1 message.selfTradeProtection
    ++ (Alpha.encode message.selfTradeProtectionGroup
    ++ (Alpha.encode message.purgeGroup
    ++ (Alpha.encode message.customerOrderHandlingInstruction
    ++ (encodeUIntLE 1 message.additionalOrderIndicators
    ++ (encodeUIntLE 4 message.minQty
    ++ (encodeUIntLE 2 message.orderExpiryDate
    ++ (encodeUIntLE 8 message.tradingCollarDollarValue
    ++ (Alpha.encode message.ctiCode
    ++ (Alpha.encode message.textMemo
    ++ (Alpha.encode message.reserved32)))))))))))))))))))))))

def decode (bytes : List UInt8) : Option (NewOrderRequestMessage × List UInt8) := do
  let (clientSendTime, bytes) ← decodeUIntLE 8 bytes
  let (mpId, bytes) ← Alpha.decode 5 bytes
  let (operatorId, bytes) ← Alpha.decode 18 bytes
  let (operatorLocation, bytes) ← Alpha.decode 6 bytes
  let (account, bytes) ← Alpha.decode 16 bytes
  let (clientOrderId, bytes) ← Alpha.decode 20 bytes
  let (instrumentIdBinaryU4, bytes) ← decodeUIntLE 4 bytes
  let (price, bytes) ← decodeUIntLE 8 bytes
  let (stopOrderTriggerPrice, bytes) ← decodeUIntLE 8 bytes
  let (sizeBinaryU4, bytes) ← decodeUIntLE 4 bytes
  let (orderInstructions, bytes) ← decodeUIntLE 2 bytes
  let (timeInForce, bytes) ← TimeInForce.decode bytes
  let (orderType, bytes) ← Alpha.decode 1 bytes
  let (selfTradeProtection, bytes) ← decodeUIntLE 1 bytes
  let (selfTradeProtectionGroup, bytes) ← Alpha.decode 2 bytes
  let (purgeGroup, bytes) ← Alpha.decode 1 bytes
  let (customerOrderHandlingInstruction, bytes) ← Alpha.decode 1 bytes
  let (additionalOrderIndicators, bytes) ← decodeUIntLE 1 bytes
  let (minQty, bytes) ← decodeUIntLE 4 bytes
  let (orderExpiryDate, bytes) ← decodeUIntLE 2 bytes
  let (tradingCollarDollarValue, bytes) ← decodeUIntLE 8 bytes
  let (ctiCode, bytes) ← Alpha.decode 1 bytes
  let (textMemo, bytes) ← Alpha.decode 20 bytes
  let (reserved32, bytes) ← Alpha.decode 32 bytes
  pure ({ clientSendTime, mpId, operatorId, operatorLocation, account, clientOrderId, instrumentIdBinaryU4, price, stopOrderTriggerPrice, sizeBinaryU4, orderInstructions, timeInForce, orderType, selfTradeProtection, selfTradeProtectionGroup, purgeGroup, customerOrderHandlingInstruction, additionalOrderIndicators, minQty, orderExpiryDate, tradingCollarDollarValue, ctiCode, textMemo, reserved32 }, bytes)

@[simp] theorem encode_length (message : NewOrderRequestMessage) : (encode message).length = 174 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length, TimeInForce.encode_length]

theorem encode_length_pos (message : NewOrderRequestMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : NewOrderRequestMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
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
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, TimeInForce.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
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
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end NewOrderRequestMessage

/-- Modify Order Request Message: 140 bytes -/
structure ModifyOrderRequestMessage where
  clientSendTime : BitVec 64
  mpId : Alpha 5
  operatorId : Alpha 18
  operatorLocation : Alpha 6
  clientOrderId : Alpha 20
  originalClientOrderId : Alpha 20
  instrumentIdBinaryU4 : BitVec 32
  price : BitVec 64
  stopOrderTriggerPrice : BitVec 64
  sizeBinaryS4 : BitVec 32
  orderExpiryDate : BitVec 16
  selfTradeProtectionGroup : Alpha 2
  purgeGroup : Alpha 1
  customerOrderHandlingInstruction : Alpha 1
  additionalOrderIndicators : BitVec 8
  reserved32 : Alpha 32
  deriving DecidableEq, Repr

namespace ModifyOrderRequestMessage

def encode (message : ModifyOrderRequestMessage) : List UInt8 :=
  encodeUIntLE 8 message.clientSendTime
    ++ (Alpha.encode message.mpId
    ++ (Alpha.encode message.operatorId
    ++ (Alpha.encode message.operatorLocation
    ++ (Alpha.encode message.clientOrderId
    ++ (Alpha.encode message.originalClientOrderId
    ++ (encodeUIntLE 4 message.instrumentIdBinaryU4
    ++ (encodeUIntLE 8 message.price
    ++ (encodeUIntLE 8 message.stopOrderTriggerPrice
    ++ (encodeUIntLE 4 message.sizeBinaryS4
    ++ (encodeUIntLE 2 message.orderExpiryDate
    ++ (Alpha.encode message.selfTradeProtectionGroup
    ++ (Alpha.encode message.purgeGroup
    ++ (Alpha.encode message.customerOrderHandlingInstruction
    ++ (encodeUIntLE 1 message.additionalOrderIndicators
    ++ (Alpha.encode message.reserved32)))))))))))))))

def decode (bytes : List UInt8) : Option (ModifyOrderRequestMessage × List UInt8) := do
  let (clientSendTime, bytes) ← decodeUIntLE 8 bytes
  let (mpId, bytes) ← Alpha.decode 5 bytes
  let (operatorId, bytes) ← Alpha.decode 18 bytes
  let (operatorLocation, bytes) ← Alpha.decode 6 bytes
  let (clientOrderId, bytes) ← Alpha.decode 20 bytes
  let (originalClientOrderId, bytes) ← Alpha.decode 20 bytes
  let (instrumentIdBinaryU4, bytes) ← decodeUIntLE 4 bytes
  let (price, bytes) ← decodeUIntLE 8 bytes
  let (stopOrderTriggerPrice, bytes) ← decodeUIntLE 8 bytes
  let (sizeBinaryS4, bytes) ← decodeUIntLE 4 bytes
  let (orderExpiryDate, bytes) ← decodeUIntLE 2 bytes
  let (selfTradeProtectionGroup, bytes) ← Alpha.decode 2 bytes
  let (purgeGroup, bytes) ← Alpha.decode 1 bytes
  let (customerOrderHandlingInstruction, bytes) ← Alpha.decode 1 bytes
  let (additionalOrderIndicators, bytes) ← decodeUIntLE 1 bytes
  let (reserved32, bytes) ← Alpha.decode 32 bytes
  pure ({ clientSendTime, mpId, operatorId, operatorLocation, clientOrderId, originalClientOrderId, instrumentIdBinaryU4, price, stopOrderTriggerPrice, sizeBinaryS4, orderExpiryDate, selfTradeProtectionGroup, purgeGroup, customerOrderHandlingInstruction, additionalOrderIndicators, reserved32 }, bytes)

@[simp] theorem encode_length (message : ModifyOrderRequestMessage) : (encode message).length = 140 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length]

theorem encode_length_pos (message : ModifyOrderRequestMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : ModifyOrderRequestMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
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
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end ModifyOrderRequestMessage

/-- Cancel Order Request Message: 99 bytes -/
structure CancelOrderRequestMessage where
  clientSendTime : BitVec 64
  mpId : Alpha 5
  operatorId : Alpha 18
  operatorLocation : Alpha 6
  orderId : BitVec 64
  clientOrderId : Alpha 20
  originalClientOrderId : Alpha 20
  instrumentIdBinaryU4 : BitVec 32
  reserved10 : Alpha 10
  deriving DecidableEq, Repr

namespace CancelOrderRequestMessage

def encode (message : CancelOrderRequestMessage) : List UInt8 :=
  encodeUIntLE 8 message.clientSendTime
    ++ (Alpha.encode message.mpId
    ++ (Alpha.encode message.operatorId
    ++ (Alpha.encode message.operatorLocation
    ++ (encodeUIntLE 8 message.orderId
    ++ (Alpha.encode message.clientOrderId
    ++ (Alpha.encode message.originalClientOrderId
    ++ (encodeUIntLE 4 message.instrumentIdBinaryU4
    ++ (Alpha.encode message.reserved10))))))))

def decode (bytes : List UInt8) : Option (CancelOrderRequestMessage × List UInt8) := do
  let (clientSendTime, bytes) ← decodeUIntLE 8 bytes
  let (mpId, bytes) ← Alpha.decode 5 bytes
  let (operatorId, bytes) ← Alpha.decode 18 bytes
  let (operatorLocation, bytes) ← Alpha.decode 6 bytes
  let (orderId, bytes) ← decodeUIntLE 8 bytes
  let (clientOrderId, bytes) ← Alpha.decode 20 bytes
  let (originalClientOrderId, bytes) ← Alpha.decode 20 bytes
  let (instrumentIdBinaryU4, bytes) ← decodeUIntLE 4 bytes
  let (reserved10, bytes) ← Alpha.decode 10 bytes
  pure ({ clientSendTime, mpId, operatorId, operatorLocation, orderId, clientOrderId, originalClientOrderId, instrumentIdBinaryU4, reserved10 }, bytes)

@[simp] theorem encode_length (message : CancelOrderRequestMessage) : (encode message).length = 99 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length]

theorem encode_length_pos (message : CancelOrderRequestMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : CancelOrderRequestMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
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
  rw [Alpha.decode_encode, some_bind]
  rfl

end CancelOrderRequestMessage

/-- Mass Cancel Request: 86 bytes -/
structure MassCancelRequest where
  clientSendTime : BitVec 64
  mpId : Alpha 5
  operatorId : Alpha 18
  operatorLocation : Alpha 6
  reserved10 : Alpha 10
  clientOrderId : Alpha 20
  scope : Alpha 1
  action : Alpha 1
  productGroupCode : Alpha 6
  productType : Alpha 1
  purgeGroup : Alpha 1
  reserved9 : Alpha 9
  deriving DecidableEq, Repr

namespace MassCancelRequest

def encode (message : MassCancelRequest) : List UInt8 :=
  encodeUIntLE 8 message.clientSendTime
    ++ (Alpha.encode message.mpId
    ++ (Alpha.encode message.operatorId
    ++ (Alpha.encode message.operatorLocation
    ++ (Alpha.encode message.reserved10
    ++ (Alpha.encode message.clientOrderId
    ++ (Alpha.encode message.scope
    ++ (Alpha.encode message.action
    ++ (Alpha.encode message.productGroupCode
    ++ (Alpha.encode message.productType
    ++ (Alpha.encode message.purgeGroup
    ++ (Alpha.encode message.reserved9)))))))))))

def decode (bytes : List UInt8) : Option (MassCancelRequest × List UInt8) := do
  let (clientSendTime, bytes) ← decodeUIntLE 8 bytes
  let (mpId, bytes) ← Alpha.decode 5 bytes
  let (operatorId, bytes) ← Alpha.decode 18 bytes
  let (operatorLocation, bytes) ← Alpha.decode 6 bytes
  let (reserved10, bytes) ← Alpha.decode 10 bytes
  let (clientOrderId, bytes) ← Alpha.decode 20 bytes
  let (scope, bytes) ← Alpha.decode 1 bytes
  let (action, bytes) ← Alpha.decode 1 bytes
  let (productGroupCode, bytes) ← Alpha.decode 6 bytes
  let (productType, bytes) ← Alpha.decode 1 bytes
  let (purgeGroup, bytes) ← Alpha.decode 1 bytes
  let (reserved9, bytes) ← Alpha.decode 9 bytes
  pure ({ clientSendTime, mpId, operatorId, operatorLocation, reserved10, clientOrderId, scope, action, productGroupCode, productType, purgeGroup, reserved9 }, bytes)

@[simp] theorem encode_length (message : MassCancelRequest) : (encode message).length = 86 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length]

theorem encode_length_pos (message : MassCancelRequest) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : MassCancelRequest) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end MassCancelRequest

/-- Strategy Leg: 16 bytes -/
structure StrategyLeg where
  instrumentIdBinaryU4 : BitVec 32
  legRatio : BitVec 32
  reserved8 : Alpha 8
  deriving DecidableEq, Repr

namespace StrategyLeg

def encode (message : StrategyLeg) : List UInt8 :=
  encodeUIntLE 4 message.instrumentIdBinaryU4
    ++ (encodeUIntLE 4 message.legRatio
    ++ (Alpha.encode message.reserved8))

def decode (bytes : List UInt8) : Option (StrategyLeg × List UInt8) := do
  let (instrumentIdBinaryU4, bytes) ← decodeUIntLE 4 bytes
  let (legRatio, bytes) ← decodeUIntLE 4 bytes
  let (reserved8, bytes) ← Alpha.decode 8 bytes
  pure ({ instrumentIdBinaryU4, legRatio, reserved8 }, bytes)

@[simp] theorem encode_length (message : StrategyLeg) : (encode message).length = 16 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length]

theorem encode_length_pos (message : StrategyLeg) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : StrategyLeg) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end StrategyLeg

/-- Strategy Creation Request -/
structure StrategyCreationRequest where
  clientSendTime : BitVec 64
  mpId : Alpha 5
  operatorId : Alpha 18
  operatorLocation : Alpha 6
  clientOrderId : Alpha 20
  reserved16 : Alpha 16
  strategyLeg : Bounded 1 StrategyLeg
  deriving DecidableEq, Repr

namespace StrategyCreationRequest

def encode (message : StrategyCreationRequest) : List UInt8 :=
  encodeUIntLE 8 message.clientSendTime
    ++ (Alpha.encode message.mpId
    ++ (Alpha.encode message.operatorId
    ++ (Alpha.encode message.operatorLocation
    ++ (Alpha.encode message.clientOrderId
    ++ (Alpha.encode message.reserved16
    ++ (encodeUIntLE 1 (BitVec.ofNat (8 * 1) message.strategyLeg.val.length)
    ++ (encodeMany StrategyLeg.encode message.strategyLeg.val)))))))

def decode (bytes : List UInt8) : Option (StrategyCreationRequest × List UInt8) := do
  let (clientSendTime, bytes) ← decodeUIntLE 8 bytes
  let (mpId, bytes) ← Alpha.decode 5 bytes
  let (operatorId, bytes) ← Alpha.decode 18 bytes
  let (operatorLocation, bytes) ← Alpha.decode 6 bytes
  let (clientOrderId, bytes) ← Alpha.decode 20 bytes
  let (reserved16, bytes) ← Alpha.decode 16 bytes
  let (numberOfLegs, bytes) ← decodeUIntLE 1 bytes
  let (strategyLeg_, bytes) ← decodeMany StrategyLeg.decode numberOfLegs.toNat bytes
  if fits_strategyLeg : strategyLeg_.length < 256 ^ 1 then
    pure ({ clientSendTime, mpId, operatorId, operatorLocation, clientOrderId, reserved16, strategyLeg := ⟨strategyLeg_, fits_strategyLeg⟩ }, bytes)
  else none

theorem encode_length_pos (message : StrategyCreationRequest) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUIntLE_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : StrategyCreationRequest) : (encode message).length ≤ 4154 := by
  have bound_strategyLeg := message.strategyLeg.length_lt
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, encodeUIntLE_length, Alpha.encode_length, encodeMany_length_const StrategyLeg.encode 16 StrategyLeg.encode_length]
  omega

@[simp] theorem decode_encode (message : StrategyCreationRequest) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeMany_bounded 1 StrategyLeg.encode StrategyLeg.decode StrategyLeg.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.strategyLeg.length_lt]
  rfl

end StrategyCreationRequest

/-- Any Unsequenced Message, selected by Unsequenced Message Type -/
inductive UnsequencedMessage where
  | newOrderRequestMessage (message : NewOrderRequestMessage) -- "N1" 0x4E31
  | newOrderResponseMessage (message : NewOrderResponseMessage) -- "NR" 0x4E52
  | modifyOrderRequestMessage (message : ModifyOrderRequestMessage) -- "M1" 0x4D31
  | modifyOrderResponse (message : ModifyOrderResponse) -- "MR" 0x4D52
  | cancelOrderRequestMessage (message : CancelOrderRequestMessage) -- "CO" 0x434F
  | cancelOrderResponse (message : CancelOrderResponse) -- "CR" 0x4352
  | massCancelRequest (message : MassCancelRequest) -- "XQ" 0x5851
  | massCancelResponse (message : MassCancelResponse) -- "XR" 0x5852
  | strategyCreationRequest (message : StrategyCreationRequest) -- "SD" 0x5344
  | strategyCreationResponseMessage (message : StrategyCreationResponseMessage) -- "SR" 0x5352
  deriving DecidableEq, Repr

namespace UnsequencedMessage

/-- The Unsequenced Message Type each message is sent under -/
def tag : UnsequencedMessage → BitVec 16
  | .newOrderRequestMessage _ => 20017
  | .newOrderResponseMessage _ => 20050
  | .modifyOrderRequestMessage _ => 19761
  | .modifyOrderResponse _ => 19794
  | .cancelOrderRequestMessage _ => 17231
  | .cancelOrderResponse _ => 17234
  | .massCancelRequest _ => 22609
  | .massCancelResponse _ => 22610
  | .strategyCreationRequest _ => 21316
  | .strategyCreationResponseMessage _ => 21330

def encode : UnsequencedMessage → List UInt8
  | .newOrderRequestMessage message => NewOrderRequestMessage.encode message
  | .newOrderResponseMessage message => NewOrderResponseMessage.encode message
  | .modifyOrderRequestMessage message => ModifyOrderRequestMessage.encode message
  | .modifyOrderResponse message => ModifyOrderResponse.encode message
  | .cancelOrderRequestMessage message => CancelOrderRequestMessage.encode message
  | .cancelOrderResponse message => CancelOrderResponse.encode message
  | .massCancelRequest message => MassCancelRequest.encode message
  | .massCancelResponse message => MassCancelResponse.encode message
  | .strategyCreationRequest message => StrategyCreationRequest.encode message
  | .strategyCreationResponseMessage message => StrategyCreationResponseMessage.encode message

/-- The most bytes any message's encoding can take -/
theorem encode_length_le (message : UnsequencedMessage) : (encode message).length ≤ 4154 := by
  cases message with
  | newOrderRequestMessage inner =>
    simp only [encode, NewOrderRequestMessage.encode_length]
    omega
  | newOrderResponseMessage inner =>
    simp only [encode, NewOrderResponseMessage.encode_length]
    omega
  | modifyOrderRequestMessage inner =>
    simp only [encode, ModifyOrderRequestMessage.encode_length]
    omega
  | modifyOrderResponse inner =>
    simp only [encode, ModifyOrderResponse.encode_length]
    omega
  | cancelOrderRequestMessage inner =>
    simp only [encode, CancelOrderRequestMessage.encode_length]
    omega
  | cancelOrderResponse inner =>
    simp only [encode, CancelOrderResponse.encode_length]
    omega
  | massCancelRequest inner =>
    simp only [encode, MassCancelRequest.encode_length]
    omega
  | massCancelResponse inner =>
    simp only [encode, MassCancelResponse.encode_length]
    omega
  | strategyCreationRequest inner =>
    have bound_inner := StrategyCreationRequest.encode_length_le inner
    simp only [encode]
    omega
  | strategyCreationResponseMessage inner =>
    simp only [encode, StrategyCreationResponseMessage.encode_length]
    omega

def decode (tag : BitVec 16) (bytes : List UInt8) : Option (UnsequencedMessage × List UInt8) :=
  if tag = 20017 then (NewOrderRequestMessage.decode bytes).map fun (message, rest) => (.newOrderRequestMessage message, rest)
  else if tag = 20050 then (NewOrderResponseMessage.decode bytes).map fun (message, rest) => (.newOrderResponseMessage message, rest)
  else if tag = 19761 then (ModifyOrderRequestMessage.decode bytes).map fun (message, rest) => (.modifyOrderRequestMessage message, rest)
  else if tag = 19794 then (ModifyOrderResponse.decode bytes).map fun (message, rest) => (.modifyOrderResponse message, rest)
  else if tag = 17231 then (CancelOrderRequestMessage.decode bytes).map fun (message, rest) => (.cancelOrderRequestMessage message, rest)
  else if tag = 17234 then (CancelOrderResponse.decode bytes).map fun (message, rest) => (.cancelOrderResponse message, rest)
  else if tag = 22609 then (MassCancelRequest.decode bytes).map fun (message, rest) => (.massCancelRequest message, rest)
  else if tag = 22610 then (MassCancelResponse.decode bytes).map fun (message, rest) => (.massCancelResponse message, rest)
  else if tag = 21316 then (StrategyCreationRequest.decode bytes).map fun (message, rest) => (.strategyCreationRequest message, rest)
  else if tag = 21330 then (StrategyCreationResponseMessage.decode bytes).map fun (message, rest) => (.strategyCreationResponseMessage message, rest)
  else none

@[simp] theorem decode_encode (message : UnsequencedMessage) (rest : List UInt8) :
    decode (tag message) (encode message ++ rest) = some (message, rest) := by
  cases message <;> simp [decode, encode, tag]

end UnsequencedMessage

/-- Unsequenced Data Packet -/
structure UnsequencedDataPacket where
  unsequencedMessage : UnsequencedMessage
  deriving DecidableEq, Repr

namespace UnsequencedDataPacket

def encode (message : UnsequencedDataPacket) : List UInt8 :=
  encodeUInt 2 (UnsequencedMessage.tag message.unsequencedMessage)
    ++ (UnsequencedMessage.encode message.unsequencedMessage)

def decode (bytes : List UInt8) : Option (UnsequencedDataPacket × List UInt8) := do
  let (unsequencedMessageType, bytes) ← decodeUInt 2 bytes
  let (unsequencedMessage, bytes) ← UnsequencedMessage.decode unsequencedMessageType bytes
  pure ({ unsequencedMessage }, bytes)

theorem encode_length_pos (message : UnsequencedDataPacket) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUInt_length, List.length_append]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : UnsequencedDataPacket) : (encode message).length ≤ 4156 := by
  unfold encode
  cases message.unsequencedMessage with
  | newOrderRequestMessage inner =>
    simp only [UnsequencedMessage.encode, List.length_append, encodeUInt_length, NewOrderRequestMessage.encode_length]
    omega
  | newOrderResponseMessage inner =>
    simp only [UnsequencedMessage.encode, List.length_append, encodeUInt_length, NewOrderResponseMessage.encode_length]
    omega
  | modifyOrderRequestMessage inner =>
    simp only [UnsequencedMessage.encode, List.length_append, encodeUInt_length, ModifyOrderRequestMessage.encode_length]
    omega
  | modifyOrderResponse inner =>
    simp only [UnsequencedMessage.encode, List.length_append, encodeUInt_length, ModifyOrderResponse.encode_length]
    omega
  | cancelOrderRequestMessage inner =>
    simp only [UnsequencedMessage.encode, List.length_append, encodeUInt_length, CancelOrderRequestMessage.encode_length]
    omega
  | cancelOrderResponse inner =>
    simp only [UnsequencedMessage.encode, List.length_append, encodeUInt_length, CancelOrderResponse.encode_length]
    omega
  | massCancelRequest inner =>
    simp only [UnsequencedMessage.encode, List.length_append, encodeUInt_length, MassCancelRequest.encode_length]
    omega
  | massCancelResponse inner =>
    simp only [UnsequencedMessage.encode, List.length_append, encodeUInt_length, MassCancelResponse.encode_length]
    omega
  | strategyCreationRequest inner =>
    have bound_inner := StrategyCreationRequest.encode_length_le inner
    simp only [UnsequencedMessage.encode, List.length_append, encodeUInt_length]
    omega
  | strategyCreationResponseMessage inner =>
    simp only [UnsequencedMessage.encode, List.length_append, encodeUInt_length, StrategyCreationResponseMessage.encode_length]
    omega

@[simp] theorem decode_encode (message : UnsequencedDataPacket) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [UnsequencedMessage.decode_encode, some_bind]
  rfl

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : UnsequencedDataPacket) : decode (encode message) = some (message, []) :=
  List.append_nil (encode message) ▸ decode_encode message []

end UnsequencedDataPacket

/-- Login Request: 35 bytes -/
structure LoginRequest where
  sesmVersion : Alpha 5
  username : Alpha 5
  computerId : Alpha 8
  applicationProtocol : Alpha 8
  requestedSession : BitVec 8
  requestedSequenceNumber : BitVec 64
  deriving DecidableEq, Repr

namespace LoginRequest

def encode (message : LoginRequest) : List UInt8 :=
  Alpha.encode message.sesmVersion
    ++ (Alpha.encode message.username
    ++ (Alpha.encode message.computerId
    ++ (Alpha.encode message.applicationProtocol
    ++ (encodeUInt 1 message.requestedSession
    ++ (encodeUIntLE 8 message.requestedSequenceNumber)))))

def decode (bytes : List UInt8) : Option (LoginRequest × List UInt8) := do
  let (sesmVersion, bytes) ← Alpha.decode 5 bytes
  let (username, bytes) ← Alpha.decode 5 bytes
  let (computerId, bytes) ← Alpha.decode 8 bytes
  let (applicationProtocol, bytes) ← Alpha.decode 8 bytes
  let (requestedSession, bytes) ← decodeUInt 1 bytes
  let (requestedSequenceNumber, bytes) ← decodeUIntLE 8 bytes
  pure ({ sesmVersion, username, computerId, applicationProtocol, requestedSession, requestedSequenceNumber }, bytes)

@[simp] theorem encode_length (message : LoginRequest) : (encode message).length = 35 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length, encodeUIntLE_length]

theorem encode_length_pos (message : LoginRequest) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : LoginRequest) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
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
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : LoginRequest) : decode (encode message) = some (message, []) :=
  List.append_nil (encode message) ▸ decode_encode message []

end LoginRequest

/-- Login Response: 10 bytes -/
structure LoginResponse where
  loginStatus : LoginStatus
  sessionId : BitVec 8
  highestSequenceNumber : BitVec 64
  deriving DecidableEq, Repr

namespace LoginResponse

def encode (message : LoginResponse) : List UInt8 :=
  LoginStatus.encode message.loginStatus
    ++ (encodeUIntLE 1 message.sessionId
    ++ (encodeUIntLE 8 message.highestSequenceNumber))

def decode (bytes : List UInt8) : Option (LoginResponse × List UInt8) := do
  let (loginStatus, bytes) ← LoginStatus.decode bytes
  let (sessionId, bytes) ← decodeUIntLE 1 bytes
  let (highestSequenceNumber, bytes) ← decodeUIntLE 8 bytes
  pure ({ loginStatus, sessionId, highestSequenceNumber }, bytes)

@[simp] theorem encode_length (message : LoginResponse) : (encode message).length = 10 := by
  unfold encode
  simp only [List.length_append, LoginStatus.encode_length, encodeUIntLE_length]

theorem encode_length_pos (message : LoginResponse) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : LoginResponse) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, LoginStatus.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : LoginResponse) : decode (encode message) = some (message, []) :=
  List.append_nil (encode message) ▸ decode_encode message []

end LoginResponse

/-- Synchronization Complete: 0 bytes -/
structure SynchronizationComplete where
  deriving DecidableEq, Repr

namespace SynchronizationComplete

def encode (_ : SynchronizationComplete) : List UInt8 :=
  []

def decode (bytes : List UInt8) : Option (SynchronizationComplete × List UInt8) :=
  some (⟨⟩, bytes)

@[simp] theorem encode_length (message : SynchronizationComplete) : (encode message).length = 0 := by
  simp [encode]

@[simp] theorem decode_encode (message : SynchronizationComplete) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  simp [decode, encode]

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : SynchronizationComplete) : decode (encode message) = some (message, []) :=
  List.append_nil (encode message) ▸ decode_encode message []

end SynchronizationComplete

/-- Retransmission Request: 16 bytes -/
structure RetransmissionRequest where
  startSequenceNumber : BitVec 64
  endSequenceNumber : BitVec 64
  deriving DecidableEq, Repr

namespace RetransmissionRequest

def encode (message : RetransmissionRequest) : List UInt8 :=
  encodeUIntLE 8 message.startSequenceNumber
    ++ (encodeUIntLE 8 message.endSequenceNumber)

def decode (bytes : List UInt8) : Option (RetransmissionRequest × List UInt8) := do
  let (startSequenceNumber, bytes) ← decodeUIntLE 8 bytes
  let (endSequenceNumber, bytes) ← decodeUIntLE 8 bytes
  pure ({ startSequenceNumber, endSequenceNumber }, bytes)

@[simp] theorem encode_length (message : RetransmissionRequest) : (encode message).length = 16 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length]

theorem encode_length_pos (message : RetransmissionRequest) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : RetransmissionRequest) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : RetransmissionRequest) : decode (encode message) = some (message, []) :=
  List.append_nil (encode message) ▸ decode_encode message []

end RetransmissionRequest

/-- Logout Request -/
structure LogoutRequest where
  logoutReason : LogoutReason
  logoutText : Capped 61378
  deriving DecidableEq, Repr

namespace LogoutRequest

def encode (message : LogoutRequest) : List UInt8 :=
  LogoutReason.encode message.logoutReason
    ++ (message.logoutText.val)

def decode (bytes : List UInt8) : Option LogoutRequest := do
  let (logoutReason, bytes) ← LogoutReason.decode bytes
  let logoutText_ := bytes
  if fits_logoutText : logoutText_.length ≤ 61378 then
    pure { logoutReason, logoutText := ⟨logoutText_, fits_logoutText⟩ }
  else none

theorem encode_length_pos (message : LogoutRequest) : (encode message).length > 0 := by
  unfold encode
  simp only [LogoutReason.encode_length, List.length_append]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : LogoutRequest) : (encode message).length ≤ 61379 := by
  have bound_logoutText := message.logoutText.length_le
  unfold encode
  simp only [List.length_append, LogoutReason.encode_length]
  omega

theorem decode_encode (message : LogoutRequest) : decode (encode message) = some message := by
  unfold decode encode
  rw [LogoutReason.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.logoutText.length_le]
  rfl

end LogoutRequest

/-- Goodbye Packet -/
structure GoodbyePacket where
  logoutReason : LogoutReason
  logoutText : Capped 61378
  deriving DecidableEq, Repr

namespace GoodbyePacket

def encode (message : GoodbyePacket) : List UInt8 :=
  LogoutReason.encode message.logoutReason
    ++ (message.logoutText.val)

def decode (bytes : List UInt8) : Option GoodbyePacket := do
  let (logoutReason, bytes) ← LogoutReason.decode bytes
  let logoutText_ := bytes
  if fits_logoutText : logoutText_.length ≤ 61378 then
    pure { logoutReason, logoutText := ⟨logoutText_, fits_logoutText⟩ }
  else none

theorem encode_length_pos (message : GoodbyePacket) : (encode message).length > 0 := by
  unfold encode
  simp only [LogoutReason.encode_length, List.length_append]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : GoodbyePacket) : (encode message).length ≤ 61379 := by
  have bound_logoutText := message.logoutText.length_le
  unfold encode
  simp only [List.length_append, LogoutReason.encode_length]
  omega

theorem decode_encode (message : GoodbyePacket) : decode (encode message) = some message := by
  unfold decode encode
  rw [LogoutReason.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.logoutText.length_le]
  rfl

end GoodbyePacket

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

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : EndOfSession) : decode (encode message) = some (message, []) :=
  List.append_nil (encode message) ▸ decode_encode message []

end EndOfSession

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

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : ServerHeartbeat) : decode (encode message) = some (message, []) :=
  List.append_nil (encode message) ▸ decode_encode message []

end ServerHeartbeat

/-- Client Heartbeat: 0 bytes -/
structure ClientHeartbeat where
  deriving DecidableEq, Repr

namespace ClientHeartbeat

def encode (_ : ClientHeartbeat) : List UInt8 :=
  []

def decode (bytes : List UInt8) : Option (ClientHeartbeat × List UInt8) :=
  some (⟨⟩, bytes)

@[simp] theorem encode_length (message : ClientHeartbeat) : (encode message).length = 0 := by
  simp [encode]

@[simp] theorem decode_encode (message : ClientHeartbeat) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  simp [decode, encode]

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : ClientHeartbeat) : decode (encode message) = some (message, []) :=
  List.append_nil (encode message) ▸ decode_encode message []

end ClientHeartbeat

/-- Any Sesm Payload, selected by Sesm Packet Type -/
inductive SesmPayload where
  | sequencedDataPacket (message : SequencedDataPacket) -- "S" 0x53
  | unsequencedDataPacket (message : UnsequencedDataPacket) -- "U" 0x55
  | loginRequest (message : LoginRequest) -- "L" 0x4C
  | loginResponse (message : LoginResponse) -- "R" 0x52
  | synchronizationComplete (message : SynchronizationComplete) -- "C" 0x43
  | retransmissionRequest (message : RetransmissionRequest) -- "A" 0x41
  | logoutRequest (message : LogoutRequest) -- "X" 0x58
  | goodbyePacket (message : GoodbyePacket) -- "G" 0x47
  | endOfSession (message : EndOfSession) -- "E" 0x45
  | serverHeartbeat (message : ServerHeartbeat) -- "0" 0x30
  | clientHeartbeat (message : ClientHeartbeat) -- "1" 0x31
  deriving DecidableEq, Repr

namespace SesmPayload

/-- The Sesm Packet Type each message is sent under -/
def tag : SesmPayload → BitVec 8
  | .sequencedDataPacket _ => 83
  | .unsequencedDataPacket _ => 85
  | .loginRequest _ => 76
  | .loginResponse _ => 82
  | .synchronizationComplete _ => 67
  | .retransmissionRequest _ => 65
  | .logoutRequest _ => 88
  | .goodbyePacket _ => 71
  | .endOfSession _ => 69
  | .serverHeartbeat _ => 48
  | .clientHeartbeat _ => 49

def encode : SesmPayload → List UInt8
  | .sequencedDataPacket message => SequencedDataPacket.encode message
  | .unsequencedDataPacket message => UnsequencedDataPacket.encode message
  | .loginRequest message => LoginRequest.encode message
  | .loginResponse message => LoginResponse.encode message
  | .synchronizationComplete message => SynchronizationComplete.encode message
  | .retransmissionRequest message => RetransmissionRequest.encode message
  | .logoutRequest message => LogoutRequest.encode message
  | .goodbyePacket message => GoodbyePacket.encode message
  | .endOfSession message => EndOfSession.encode message
  | .serverHeartbeat message => ServerHeartbeat.encode message
  | .clientHeartbeat message => ClientHeartbeat.encode message

/-- The most bytes any message's encoding can take -/
theorem encode_length_le (message : SesmPayload) : (encode message).length ≤ 61379 := by
  cases message with
  | sequencedDataPacket inner =>
    have bound_inner := SequencedDataPacket.encode_length_le inner
    simp only [encode]
    omega
  | unsequencedDataPacket inner =>
    have bound_inner := UnsequencedDataPacket.encode_length_le inner
    simp only [encode]
    omega
  | loginRequest inner =>
    simp only [encode, LoginRequest.encode_length]
    omega
  | loginResponse inner =>
    simp only [encode, LoginResponse.encode_length]
    omega
  | synchronizationComplete inner =>
    simp only [encode, SynchronizationComplete.encode_length]
    omega
  | retransmissionRequest inner =>
    simp only [encode, RetransmissionRequest.encode_length]
    omega
  | logoutRequest inner =>
    have bound_inner := LogoutRequest.encode_length_le inner
    simp only [encode]
    omega
  | goodbyePacket inner =>
    have bound_inner := GoodbyePacket.encode_length_le inner
    simp only [encode]
    omega
  | endOfSession inner =>
    simp only [encode, EndOfSession.encode_length]
    omega
  | serverHeartbeat inner =>
    simp only [encode, ServerHeartbeat.encode_length]
    omega
  | clientHeartbeat inner =>
    simp only [encode, ClientHeartbeat.encode_length]
    omega

/-- Decoded from the whole of the frame: a message that reads to its end takes it all, any other must leave nothing -/
def decode (tag : BitVec 8) (bytes : List UInt8) : Option SesmPayload :=
  if tag = 83 then (SequencedDataPacket.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.sequencedDataPacket message) else none
  else if tag = 85 then (UnsequencedDataPacket.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.unsequencedDataPacket message) else none
  else if tag = 76 then (LoginRequest.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.loginRequest message) else none
  else if tag = 82 then (LoginResponse.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.loginResponse message) else none
  else if tag = 67 then (SynchronizationComplete.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.synchronizationComplete message) else none
  else if tag = 65 then (RetransmissionRequest.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.retransmissionRequest message) else none
  else if tag = 88 then (LogoutRequest.decode bytes).map fun message => .logoutRequest message
  else if tag = 71 then (GoodbyePacket.decode bytes).map fun message => .goodbyePacket message
  else if tag = 69 then (EndOfSession.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.endOfSession message) else none
  else if tag = 48 then (ServerHeartbeat.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.serverHeartbeat message) else none
  else if tag = 49 then (ClientHeartbeat.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.clientHeartbeat message) else none
  else none

theorem decode_encode (message : SesmPayload) :
    decode (tag message) (encode message) = some message := by
  cases message with
  | sequencedDataPacket message => simp [decode, encode, tag, SequencedDataPacket.decode_encode_nil]
  | unsequencedDataPacket message => simp [decode, encode, tag, UnsequencedDataPacket.decode_encode_nil]
  | loginRequest message => simp [decode, encode, tag, LoginRequest.decode_encode_nil]
  | loginResponse message => simp [decode, encode, tag, LoginResponse.decode_encode_nil]
  | synchronizationComplete message => simp [decode, encode, tag, SynchronizationComplete.decode_encode_nil]
  | retransmissionRequest message => simp [decode, encode, tag, RetransmissionRequest.decode_encode_nil]
  | logoutRequest message => simp [decode, encode, tag, LogoutRequest.decode_encode]
  | goodbyePacket message => simp [decode, encode, tag, GoodbyePacket.decode_encode]
  | endOfSession message => simp [decode, encode, tag, EndOfSession.decode_encode_nil]
  | serverHeartbeat message => simp [decode, encode, tag, ServerHeartbeat.decode_encode_nil]
  | clientHeartbeat message => simp [decode, encode, tag, ClientHeartbeat.decode_encode_nil]

end SesmPayload

/-- Sesm Tcp Packet -/
structure SesmTcpPacket where
  sesmPayload : SesmPayload
  deriving DecidableEq, Repr

namespace SesmTcpPacket

def encodeBody (message : SesmTcpPacket) : List UInt8 :=
  encodeUInt 1 (SesmPayload.tag message.sesmPayload)
    ++ (SesmPayload.encode message.sesmPayload)

def decodeBody (bytes : List UInt8) : Option SesmTcpPacket := do
  let (sesmPacketType, bytes) ← decodeUInt 1 bytes
  let sesmPayload ← SesmPayload.decode sesmPacketType bytes
  pure { sesmPayload }

theorem decodeBody_encodeBody (message : SesmTcpPacket) : decodeBody (encodeBody message) = some message := by
  unfold decodeBody encodeBody
  rw [decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [SesmPayload.decode_encode, some_bind]
  rfl

/-- Every body fits the length prefix -/
theorem encodeBody_length_lt (message : SesmTcpPacket) : (encodeBody message).length + 0 < 256 ^ 2 := by
  unfold encodeBody
  cases message.sesmPayload with
  | sequencedDataPacket inner =>
    have bound_inner := SequencedDataPacket.encode_length_le inner
    simp only [SesmPayload.encode, List.length_append, encodeUInt_length]
    omega
  | unsequencedDataPacket inner =>
    have bound_inner := UnsequencedDataPacket.encode_length_le inner
    simp only [SesmPayload.encode, List.length_append, encodeUInt_length]
    omega
  | loginRequest inner =>
    simp only [SesmPayload.encode, List.length_append, encodeUInt_length, LoginRequest.encode_length]
    omega
  | loginResponse inner =>
    simp only [SesmPayload.encode, List.length_append, encodeUInt_length, LoginResponse.encode_length]
    omega
  | synchronizationComplete inner =>
    simp only [SesmPayload.encode, List.length_append, encodeUInt_length, SynchronizationComplete.encode_length]
    omega
  | retransmissionRequest inner =>
    simp only [SesmPayload.encode, List.length_append, encodeUInt_length, RetransmissionRequest.encode_length]
    omega
  | logoutRequest inner =>
    have bound_inner := LogoutRequest.encode_length_le inner
    simp only [SesmPayload.encode, List.length_append, encodeUInt_length]
    omega
  | goodbyePacket inner =>
    have bound_inner := GoodbyePacket.encode_length_le inner
    simp only [SesmPayload.encode, List.length_append, encodeUInt_length]
    omega
  | endOfSession inner =>
    simp only [SesmPayload.encode, List.length_append, encodeUInt_length, EndOfSession.encode_length]
    omega
  | serverHeartbeat inner =>
    simp only [SesmPayload.encode, List.length_append, encodeUInt_length, ServerHeartbeat.encode_length]
    omega
  | clientHeartbeat inner =>
    simp only [SesmPayload.encode, List.length_append, encodeUInt_length, ClientHeartbeat.encode_length]
    omega

/-- Size rule: Sesm Packet Length counts the bytes after it, so it is written from the body and checked on decode -/
def encode : SesmTcpPacket → List UInt8 :=
  encodeFramedLE 2 0 encodeBody

def decode : List UInt8 → Option (SesmTcpPacket × List UInt8) :=
  decodeFramedAllLE 2 0 decodeBody

@[simp] theorem decode_encode (message : SesmTcpPacket) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) :=
  decodeFramedAllLE_encodeFramedLE 2 0 encodeBody decodeBody message (decodeBody_encodeBody message) (encodeBody_length_lt message) rest

theorem encode_length_pos (message : SesmTcpPacket) : (encode message).length > 0 := by
  unfold encode
  rw [encodeFramedLE_length]
  omega

end SesmTcpPacket

/-- Packet -/
structure Packet where
  sesmTcpPacket : List SesmTcpPacket
  deriving DecidableEq, Repr

namespace Packet

def encode (message : Packet) : List UInt8 :=
  encodeMany SesmTcpPacket.encode message.sesmTcpPacket

def decode (bytes : List UInt8) : Option Packet := do
  let sesmTcpPacket ← decodeAll SesmTcpPacket.decode bytes.length bytes
  pure { sesmTcpPacket }

theorem decode_encode (message : Packet) : decode (encode message) = some message := by
  unfold decode encode
  rw [decodeAll_encodeMany SesmTcpPacket.encode SesmTcpPacket.decode SesmTcpPacket.decode_encode SesmTcpPacket.encode_length_pos message.sesmTcpPacket _ (encodeMany_length_ge SesmTcpPacket.encode SesmTcpPacket.encode_length_pos message.sesmTcpPacket), some_bind]
  rfl

end Packet

end Omi.MiaxOnyxfuturesExpressinterfaceFeiV10C
