import Wire

/-!
# London Stock Exchange Native Trading Gateway v21.2

Generated from the binary model, with the proofs the model's rules call for: every record
decodes back to what was encoded; a message dispatch selects the message its type names;
a count is written from the list it counts; a length prefix is written from the bytes it frames;
and a packet read to the end of its data decodes to the messages that were written.

Text fields are kept byte for byte, padding included, so what is decoded encodes back unchanged.
Prices with implied decimals are proven as the integers on the wire.
-/

namespace Omi.LsegMillenniumNativetradinggatewayNtgiV212

/-- Exec Type: one byte code -/
def ExecType.codes : List UInt8 :=
  [0x30, 0x34, 0x35, 0x38, 0x43, 0x44, 0x46, 0x48, 0x39]

inductive ExecType where
  | new -- New
  | cancelled -- Cancelled
  | replaced -- Replaced
  | rejected -- Rejected
  | expired -- Expired
  | restated -- Restated
  | trade -- Trade
  | tradeCancel -- Trade Cancel
  | suspended -- Suspended
  | unlisted (byte : { byte : UInt8 // byte ∉ ExecType.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace ExecType

def toByte : ExecType → UInt8
  | .new => 0x30
  | .cancelled => 0x34
  | .replaced => 0x35
  | .rejected => 0x38
  | .expired => 0x43
  | .restated => 0x44
  | .trade => 0x46
  | .tradeCancel => 0x48
  | .suspended => 0x39
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : ExecType :=
  if byte = 0x30 then .new
  else if byte = 0x34 then .cancelled
  else if byte = 0x35 then .replaced
  else if byte = 0x38 then .rejected
  else if byte = 0x43 then .expired
  else if byte = 0x44 then .restated
  else if byte = 0x46 then .trade
  else if byte = 0x48 then .tradeCancel
  else .suspended

def ofByte (byte : UInt8) : ExecType :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : ExecType) : ofByte value.toByte = value := by
  cases value with
  | new => decide
  | cancelled => decide
  | replaced => decide
  | rejected => decide
  | expired => decide
  | restated => decide
  | trade => decide
  | tradeCancel => decide
  | suspended => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : ExecType) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (ExecType × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : ExecType) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : ExecType) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end ExecType

/-- Trade Liquidity Indicator: one byte code -/
def TradeLiquidityIndicator.codes : List UInt8 :=
  [0x41, 0x52, 0x43]

inductive TradeLiquidityIndicator where
  | addedLiquidity -- Added Liquidity
  | removedLiquidity -- Removed Liquidity
  | auction -- Auction
  | unlisted (byte : { byte : UInt8 // byte ∉ TradeLiquidityIndicator.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace TradeLiquidityIndicator

def toByte : TradeLiquidityIndicator → UInt8
  | .addedLiquidity => 0x41
  | .removedLiquidity => 0x52
  | .auction => 0x43
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : TradeLiquidityIndicator :=
  if byte = 0x41 then .addedLiquidity
  else if byte = 0x52 then .removedLiquidity
  else .auction

def ofByte (byte : UInt8) : TradeLiquidityIndicator :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : TradeLiquidityIndicator) : ofByte value.toByte = value := by
  cases value with
  | addedLiquidity => decide
  | removedLiquidity => decide
  | auction => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : TradeLiquidityIndicator) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (TradeLiquidityIndicator × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : TradeLiquidityIndicator) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : TradeLiquidityIndicator) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end TradeLiquidityIndicator

/-- Execution Type: one byte code -/
def ExecutionType.codes : List UInt8 :=
  [0x34, 0x43, 0x44, 0x46, 0x48]

inductive ExecutionType where
  | cancelled -- Cancelled
  | expired -- Expired
  | restated -- Restated
  | trade -- Trade
  | tradeCancel -- Trade Cancel
  | unlisted (byte : { byte : UInt8 // byte ∉ ExecutionType.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace ExecutionType

def toByte : ExecutionType → UInt8
  | .cancelled => 0x34
  | .expired => 0x43
  | .restated => 0x44
  | .trade => 0x46
  | .tradeCancel => 0x48
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : ExecutionType :=
  if byte = 0x34 then .cancelled
  else if byte = 0x43 then .expired
  else if byte = 0x44 then .restated
  else if byte = 0x46 then .trade
  else .tradeCancel

def ofByte (byte : UInt8) : ExecutionType :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : ExecutionType) : ofByte value.toByte = value := by
  cases value with
  | cancelled => decide
  | expired => decide
  | restated => decide
  | trade => decide
  | tradeCancel => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : ExecutionType) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (ExecutionType × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : ExecutionType) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : ExecutionType) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end ExecutionType

/-- Logon Message: 76 bytes -/
structure LogonMessage where
  userName : Alpha 25
  password : Alpha 25
  newPassword : Alpha 25
  messageVersion : BitVec 8
  deriving DecidableEq, Repr

namespace LogonMessage

def encode (message : LogonMessage) : List UInt8 :=
  Alpha.encode message.userName
    ++ (Alpha.encode message.password
    ++ (Alpha.encode message.newPassword
    ++ (encodeUIntLE 1 message.messageVersion)))

def decode (bytes : List UInt8) : Option (LogonMessage × List UInt8) := do
  let (userName, bytes) ← Alpha.decode 25 bytes
  let (password, bytes) ← Alpha.decode 25 bytes
  let (newPassword, bytes) ← Alpha.decode 25 bytes
  let (messageVersion, bytes) ← decodeUIntLE 1 bytes
  pure ({ userName, password, newPassword, messageVersion }, bytes)

@[simp] theorem encode_length (message : LogonMessage) : (encode message).length = 76 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUIntLE_length]

theorem encode_length_pos (message : LogonMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : LogonMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end LogonMessage

/-- Logon Reply Message: 34 bytes -/
structure LogonReplyMessage where
  rejectCode : BitVec 32
  passwordExpiryDayCount : Alpha 30
  deriving DecidableEq, Repr

namespace LogonReplyMessage

def encode (message : LogonReplyMessage) : List UInt8 :=
  encodeUIntLE 4 message.rejectCode
    ++ (Alpha.encode message.passwordExpiryDayCount)

def decode (bytes : List UInt8) : Option (LogonReplyMessage × List UInt8) := do
  let (rejectCode, bytes) ← decodeUIntLE 4 bytes
  let (passwordExpiryDayCount, bytes) ← Alpha.decode 30 bytes
  pure ({ rejectCode, passwordExpiryDayCount }, bytes)

@[simp] theorem encode_length (message : LogonReplyMessage) : (encode message).length = 34 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length]

theorem encode_length_pos (message : LogonReplyMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : LogonReplyMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end LogonReplyMessage

/-- Logout Message: 20 bytes -/
structure LogoutMessage where
  reason : Alpha 20
  deriving DecidableEq, Repr

namespace LogoutMessage

def encode (message : LogoutMessage) : List UInt8 :=
  Alpha.encode message.reason

def decode (bytes : List UInt8) : Option (LogoutMessage × List UInt8) := do
  let (reason, bytes) ← Alpha.decode 20 bytes
  pure ({ reason }, bytes)

@[simp] theorem encode_length (message : LogoutMessage) : (encode message).length = 20 := by
  unfold encode
  simp only [Alpha.encode_length]

theorem encode_length_pos (message : LogoutMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : LogoutMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [Alpha.decode_encode, some_bind]
  rfl

end LogoutMessage

/-- Heartbeat Message: 0 bytes -/
structure HeartbeatMessage where
  deriving DecidableEq, Repr

namespace HeartbeatMessage

def encode (_ : HeartbeatMessage) : List UInt8 :=
  []

def decode (bytes : List UInt8) : Option (HeartbeatMessage × List UInt8) :=
  some (⟨⟩, bytes)

@[simp] theorem encode_length (message : HeartbeatMessage) : (encode message).length = 0 := by
  simp [encode]

@[simp] theorem decode_encode (message : HeartbeatMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  simp [decode, encode]

end HeartbeatMessage

/-- Reject Message: 55 bytes -/
structure RejectMessage where
  rejectCode : BitVec 32
  rejectReason : Alpha 30
  rejectedMessageType : Alpha 1
  clientOrderId : Alpha 20
  deriving DecidableEq, Repr

namespace RejectMessage

def encode (message : RejectMessage) : List UInt8 :=
  encodeUIntLE 4 message.rejectCode
    ++ (Alpha.encode message.rejectReason
    ++ (Alpha.encode message.rejectedMessageType
    ++ (Alpha.encode message.clientOrderId)))

def decode (bytes : List UInt8) : Option (RejectMessage × List UInt8) := do
  let (rejectCode, bytes) ← decodeUIntLE 4 bytes
  let (rejectReason, bytes) ← Alpha.decode 30 bytes
  let (rejectedMessageType, bytes) ← Alpha.decode 1 bytes
  let (clientOrderId, bytes) ← Alpha.decode 20 bytes
  pure ({ rejectCode, rejectReason, rejectedMessageType, clientOrderId }, bytes)

@[simp] theorem encode_length (message : RejectMessage) : (encode message).length = 55 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length]

theorem encode_length_pos (message : RejectMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : RejectMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end RejectMessage

/-- System Status Message: 2 bytes -/
structure SystemStatusMessage where
  appId : BitVec 8
  appStatus : BitVec 8
  deriving DecidableEq, Repr

namespace SystemStatusMessage

def encode (message : SystemStatusMessage) : List UInt8 :=
  encodeUIntLE 1 message.appId
    ++ (encodeUIntLE 1 message.appStatus)

def decode (bytes : List UInt8) : Option (SystemStatusMessage × List UInt8) := do
  let (appId, bytes) ← decodeUIntLE 1 bytes
  let (appStatus, bytes) ← decodeUIntLE 1 bytes
  pure ({ appId, appStatus }, bytes)

@[simp] theorem encode_length (message : SystemStatusMessage) : (encode message).length = 2 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length]

theorem encode_length_pos (message : SystemStatusMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SystemStatusMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end SystemStatusMessage

/-- New Order Message: 121 bytes -/
structure NewOrderMessage where
  clientOrderId : Alpha 20
  traderId : Alpha 11
  account : Alpha 10
  clearingAccount : BitVec 8
  instrumentId : BitVec 32
  miFidFlags : BitVec 8
  partyRoleQualifiers : BitVec 8
  orderType : BitVec 8
  tif : BitVec 8
  expireDateTime : BitVec 32
  side : BitVec 8
  orderQty : BitVec 32
  displayQty : BitVec 32
  limitPrice : BitVec 64
  capacity : BitVec 8
  autoCancel : BitVec 8
  newOrderOrderSubType : BitVec 8
  anonymity : BitVec 8
  stopPrice : BitVec 64
  passiveOnlyOrder : BitVec 8
  clientId : BitVec 32
  investmentDecisionMaker : BitVec 32
  groupId : BitVec 8
  minimumQuantity : BitVec 32
  executingTrader : BitVec 32
  offset : BitVec 32
  newOrderPeggedExecInst : BitVec 8
  ownerType : BitVec 8
  reserved14 : Alpha 14
  deriving DecidableEq, Repr

namespace NewOrderMessage

def encode (message : NewOrderMessage) : List UInt8 :=
  Alpha.encode message.clientOrderId
    ++ (Alpha.encode message.traderId
    ++ (Alpha.encode message.account
    ++ (encodeUIntLE 1 message.clearingAccount
    ++ (encodeUIntLE 4 message.instrumentId
    ++ (encodeUIntLE 1 message.miFidFlags
    ++ (encodeUIntLE 1 message.partyRoleQualifiers
    ++ (encodeUIntLE 1 message.orderType
    ++ (encodeUIntLE 1 message.tif
    ++ (encodeUIntLE 4 message.expireDateTime
    ++ (encodeUIntLE 1 message.side
    ++ (encodeUIntLE 4 message.orderQty
    ++ (encodeUIntLE 4 message.displayQty
    ++ (encodeUIntLE 8 message.limitPrice
    ++ (encodeUIntLE 1 message.capacity
    ++ (encodeUIntLE 1 message.autoCancel
    ++ (encodeUIntLE 1 message.newOrderOrderSubType
    ++ (encodeUIntLE 1 message.anonymity
    ++ (encodeUIntLE 8 message.stopPrice
    ++ (encodeUIntLE 1 message.passiveOnlyOrder
    ++ (encodeUIntLE 4 message.clientId
    ++ (encodeUIntLE 4 message.investmentDecisionMaker
    ++ (encodeUIntLE 1 message.groupId
    ++ (encodeUIntLE 4 message.minimumQuantity
    ++ (encodeUIntLE 4 message.executingTrader
    ++ (encodeUIntLE 4 message.offset
    ++ (encodeUIntLE 1 message.newOrderPeggedExecInst
    ++ (encodeUIntLE 1 message.ownerType
    ++ (Alpha.encode message.reserved14))))))))))))))))))))))))))))

-- a long run of fields nests deeper than the elaborator's default limit
set_option maxRecDepth 4096 in
def decode (bytes : List UInt8) : Option (NewOrderMessage × List UInt8) := do
  let (clientOrderId, bytes) ← Alpha.decode 20 bytes
  let (traderId, bytes) ← Alpha.decode 11 bytes
  let (account, bytes) ← Alpha.decode 10 bytes
  let (clearingAccount, bytes) ← decodeUIntLE 1 bytes
  let (instrumentId, bytes) ← decodeUIntLE 4 bytes
  let (miFidFlags, bytes) ← decodeUIntLE 1 bytes
  let (partyRoleQualifiers, bytes) ← decodeUIntLE 1 bytes
  let (orderType, bytes) ← decodeUIntLE 1 bytes
  let (tif, bytes) ← decodeUIntLE 1 bytes
  let (expireDateTime, bytes) ← decodeUIntLE 4 bytes
  let (side, bytes) ← decodeUIntLE 1 bytes
  let (orderQty, bytes) ← decodeUIntLE 4 bytes
  let (displayQty, bytes) ← decodeUIntLE 4 bytes
  let (limitPrice, bytes) ← decodeUIntLE 8 bytes
  let (capacity, bytes) ← decodeUIntLE 1 bytes
  let (autoCancel, bytes) ← decodeUIntLE 1 bytes
  let (newOrderOrderSubType, bytes) ← decodeUIntLE 1 bytes
  let (anonymity, bytes) ← decodeUIntLE 1 bytes
  let (stopPrice, bytes) ← decodeUIntLE 8 bytes
  let (passiveOnlyOrder, bytes) ← decodeUIntLE 1 bytes
  let (clientId, bytes) ← decodeUIntLE 4 bytes
  let (investmentDecisionMaker, bytes) ← decodeUIntLE 4 bytes
  let (groupId, bytes) ← decodeUIntLE 1 bytes
  let (minimumQuantity, bytes) ← decodeUIntLE 4 bytes
  let (executingTrader, bytes) ← decodeUIntLE 4 bytes
  let (offset, bytes) ← decodeUIntLE 4 bytes
  let (newOrderPeggedExecInst, bytes) ← decodeUIntLE 1 bytes
  let (ownerType, bytes) ← decodeUIntLE 1 bytes
  let (reserved14, bytes) ← Alpha.decode 14 bytes
  pure ({ clientOrderId, traderId, account, clearingAccount, instrumentId, miFidFlags, partyRoleQualifiers, orderType, tif, expireDateTime, side, orderQty, displayQty, limitPrice, capacity, autoCancel, newOrderOrderSubType, anonymity, stopPrice, passiveOnlyOrder, clientId, investmentDecisionMaker, groupId, minimumQuantity, executingTrader, offset, newOrderPeggedExecInst, ownerType, reserved14 }, bytes)

@[simp] theorem encode_length (message : NewOrderMessage) : (encode message).length = 121 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUIntLE_length]

theorem encode_length_pos (message : NewOrderMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

set_option maxRecDepth 4096 in
@[simp] theorem decode_encode (message : NewOrderMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
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

end NewOrderMessage

/-- New Quote Message: 77 bytes -/
structure NewQuoteMessage where
  clientOrderId : Alpha 20
  traderId : Alpha 11
  clearingAccount : BitVec 8
  instrumentId : BitVec 32
  bidPrice : BitVec 64
  bidSize : BitVec 32
  askPrice : BitVec 64
  askSize : BitVec 32
  capacity : BitVec 8
  autoCancel : BitVec 8
  clientId : BitVec 32
  investmentDecisionMaker : BitVec 32
  executingTrader : BitVec 32
  miFidFlags : BitVec 8
  partyRoleQualifiers : BitVec 8
  newQuotePeggedExecInst : BitVec 8
  deriving DecidableEq, Repr

namespace NewQuoteMessage

def encode (message : NewQuoteMessage) : List UInt8 :=
  Alpha.encode message.clientOrderId
    ++ (Alpha.encode message.traderId
    ++ (encodeUIntLE 1 message.clearingAccount
    ++ (encodeUIntLE 4 message.instrumentId
    ++ (encodeUIntLE 8 message.bidPrice
    ++ (encodeUIntLE 4 message.bidSize
    ++ (encodeUIntLE 8 message.askPrice
    ++ (encodeUIntLE 4 message.askSize
    ++ (encodeUIntLE 1 message.capacity
    ++ (encodeUIntLE 1 message.autoCancel
    ++ (encodeUIntLE 4 message.clientId
    ++ (encodeUIntLE 4 message.investmentDecisionMaker
    ++ (encodeUIntLE 4 message.executingTrader
    ++ (encodeUIntLE 1 message.miFidFlags
    ++ (encodeUIntLE 1 message.partyRoleQualifiers
    ++ (encodeUIntLE 1 message.newQuotePeggedExecInst)))))))))))))))

def decode (bytes : List UInt8) : Option (NewQuoteMessage × List UInt8) := do
  let (clientOrderId, bytes) ← Alpha.decode 20 bytes
  let (traderId, bytes) ← Alpha.decode 11 bytes
  let (clearingAccount, bytes) ← decodeUIntLE 1 bytes
  let (instrumentId, bytes) ← decodeUIntLE 4 bytes
  let (bidPrice, bytes) ← decodeUIntLE 8 bytes
  let (bidSize, bytes) ← decodeUIntLE 4 bytes
  let (askPrice, bytes) ← decodeUIntLE 8 bytes
  let (askSize, bytes) ← decodeUIntLE 4 bytes
  let (capacity, bytes) ← decodeUIntLE 1 bytes
  let (autoCancel, bytes) ← decodeUIntLE 1 bytes
  let (clientId, bytes) ← decodeUIntLE 4 bytes
  let (investmentDecisionMaker, bytes) ← decodeUIntLE 4 bytes
  let (executingTrader, bytes) ← decodeUIntLE 4 bytes
  let (miFidFlags, bytes) ← decodeUIntLE 1 bytes
  let (partyRoleQualifiers, bytes) ← decodeUIntLE 1 bytes
  let (newQuotePeggedExecInst, bytes) ← decodeUIntLE 1 bytes
  pure ({ clientOrderId, traderId, clearingAccount, instrumentId, bidPrice, bidSize, askPrice, askSize, capacity, autoCancel, clientId, investmentDecisionMaker, executingTrader, miFidFlags, partyRoleQualifiers, newQuotePeggedExecInst }, bytes)

@[simp] theorem encode_length (message : NewQuoteMessage) : (encode message).length = 77 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUIntLE_length]

theorem encode_length_pos (message : NewQuoteMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : NewQuoteMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
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
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end NewQuoteMessage

/-- Order Cancel Replace Request Message: 112 bytes -/
structure OrderCancelReplaceRequestMessage where
  clientOrderId : Alpha 20
  originalClientOrderId : Alpha 20
  orderId : Alpha 12
  instrumentId : BitVec 32
  groupId : BitVec 8
  reserved1 : Alpha 1
  expireDateTime : BitVec 32
  orderQty : BitVec 32
  displayQty : BitVec 32
  limitPrice : BitVec 64
  account : Alpha 10
  secondReserved1 : Alpha 1
  side : BitVec 8
  stopPrice : BitVec 64
  passiveOnlyOrder : BitVec 8
  offset : BitVec 32
  reserved5 : Alpha 5
  minimumQuantity : BitVec 32
  deriving DecidableEq, Repr

namespace OrderCancelReplaceRequestMessage

def encode (message : OrderCancelReplaceRequestMessage) : List UInt8 :=
  Alpha.encode message.clientOrderId
    ++ (Alpha.encode message.originalClientOrderId
    ++ (Alpha.encode message.orderId
    ++ (encodeUIntLE 4 message.instrumentId
    ++ (encodeUIntLE 1 message.groupId
    ++ (Alpha.encode message.reserved1
    ++ (encodeUIntLE 4 message.expireDateTime
    ++ (encodeUIntLE 4 message.orderQty
    ++ (encodeUIntLE 4 message.displayQty
    ++ (encodeUIntLE 8 message.limitPrice
    ++ (Alpha.encode message.account
    ++ (Alpha.encode message.secondReserved1
    ++ (encodeUIntLE 1 message.side
    ++ (encodeUIntLE 8 message.stopPrice
    ++ (encodeUIntLE 1 message.passiveOnlyOrder
    ++ (encodeUIntLE 4 message.offset
    ++ (Alpha.encode message.reserved5
    ++ (encodeUIntLE 4 message.minimumQuantity)))))))))))))))))

def decode (bytes : List UInt8) : Option (OrderCancelReplaceRequestMessage × List UInt8) := do
  let (clientOrderId, bytes) ← Alpha.decode 20 bytes
  let (originalClientOrderId, bytes) ← Alpha.decode 20 bytes
  let (orderId, bytes) ← Alpha.decode 12 bytes
  let (instrumentId, bytes) ← decodeUIntLE 4 bytes
  let (groupId, bytes) ← decodeUIntLE 1 bytes
  let (reserved1, bytes) ← Alpha.decode 1 bytes
  let (expireDateTime, bytes) ← decodeUIntLE 4 bytes
  let (orderQty, bytes) ← decodeUIntLE 4 bytes
  let (displayQty, bytes) ← decodeUIntLE 4 bytes
  let (limitPrice, bytes) ← decodeUIntLE 8 bytes
  let (account, bytes) ← Alpha.decode 10 bytes
  let (secondReserved1, bytes) ← Alpha.decode 1 bytes
  let (side, bytes) ← decodeUIntLE 1 bytes
  let (stopPrice, bytes) ← decodeUIntLE 8 bytes
  let (passiveOnlyOrder, bytes) ← decodeUIntLE 1 bytes
  let (offset, bytes) ← decodeUIntLE 4 bytes
  let (reserved5, bytes) ← Alpha.decode 5 bytes
  let (minimumQuantity, bytes) ← decodeUIntLE 4 bytes
  pure ({ clientOrderId, originalClientOrderId, orderId, instrumentId, groupId, reserved1, expireDateTime, orderQty, displayQty, limitPrice, account, secondReserved1, side, stopPrice, passiveOnlyOrder, offset, reserved5, minimumQuantity }, bytes)

@[simp] theorem encode_length (message : OrderCancelReplaceRequestMessage) : (encode message).length = 112 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUIntLE_length]

theorem encode_length_pos (message : OrderCancelReplaceRequestMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OrderCancelReplaceRequestMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
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
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end OrderCancelReplaceRequestMessage

/-- Order Cancel Request Message: 69 bytes -/
structure OrderCancelRequestMessage where
  clientOrderId : Alpha 20
  originalClientOrderId : Alpha 20
  orderId : Alpha 12
  instrumentId : BitVec 32
  reserved1 : Alpha 1
  secondReserved1 : Alpha 1
  side : BitVec 8
  rfqId : Alpha 10
  deriving DecidableEq, Repr

namespace OrderCancelRequestMessage

def encode (message : OrderCancelRequestMessage) : List UInt8 :=
  Alpha.encode message.clientOrderId
    ++ (Alpha.encode message.originalClientOrderId
    ++ (Alpha.encode message.orderId
    ++ (encodeUIntLE 4 message.instrumentId
    ++ (Alpha.encode message.reserved1
    ++ (Alpha.encode message.secondReserved1
    ++ (encodeUIntLE 1 message.side
    ++ (Alpha.encode message.rfqId)))))))

def decode (bytes : List UInt8) : Option (OrderCancelRequestMessage × List UInt8) := do
  let (clientOrderId, bytes) ← Alpha.decode 20 bytes
  let (originalClientOrderId, bytes) ← Alpha.decode 20 bytes
  let (orderId, bytes) ← Alpha.decode 12 bytes
  let (instrumentId, bytes) ← decodeUIntLE 4 bytes
  let (reserved1, bytes) ← Alpha.decode 1 bytes
  let (secondReserved1, bytes) ← Alpha.decode 1 bytes
  let (side, bytes) ← decodeUIntLE 1 bytes
  let (rfqId, bytes) ← Alpha.decode 10 bytes
  pure ({ clientOrderId, originalClientOrderId, orderId, instrumentId, reserved1, secondReserved1, side, rfqId }, bytes)

@[simp] theorem encode_length (message : OrderCancelRequestMessage) : (encode message).length = 69 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUIntLE_length]

theorem encode_length_pos (message : OrderCancelRequestMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OrderCancelRequestMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
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

end OrderCancelRequestMessage

/-- Order Mass Cancel Request Message: 42 bytes -/
structure OrderMassCancelRequestMessage where
  clientOrderId : Alpha 20
  massCancelRequestType : BitVec 8
  instrumentId : BitVec 32
  reserved1 : Alpha 1
  groupId : BitVec 8
  segment : Alpha 4
  orderMassCancelRequestOrderSubType : BitVec 8
  reserved10 : Alpha 10
  deriving DecidableEq, Repr

namespace OrderMassCancelRequestMessage

def encode (message : OrderMassCancelRequestMessage) : List UInt8 :=
  Alpha.encode message.clientOrderId
    ++ (encodeUIntLE 1 message.massCancelRequestType
    ++ (encodeUIntLE 4 message.instrumentId
    ++ (Alpha.encode message.reserved1
    ++ (encodeUIntLE 1 message.groupId
    ++ (Alpha.encode message.segment
    ++ (encodeUIntLE 1 message.orderMassCancelRequestOrderSubType
    ++ (Alpha.encode message.reserved10)))))))

def decode (bytes : List UInt8) : Option (OrderMassCancelRequestMessage × List UInt8) := do
  let (clientOrderId, bytes) ← Alpha.decode 20 bytes
  let (massCancelRequestType, bytes) ← decodeUIntLE 1 bytes
  let (instrumentId, bytes) ← decodeUIntLE 4 bytes
  let (reserved1, bytes) ← Alpha.decode 1 bytes
  let (groupId, bytes) ← decodeUIntLE 1 bytes
  let (segment, bytes) ← Alpha.decode 4 bytes
  let (orderMassCancelRequestOrderSubType, bytes) ← decodeUIntLE 1 bytes
  let (reserved10, bytes) ← Alpha.decode 10 bytes
  pure ({ clientOrderId, massCancelRequestType, instrumentId, reserved1, groupId, segment, orderMassCancelRequestOrderSubType, reserved10 }, bytes)

@[simp] theorem encode_length (message : OrderMassCancelRequestMessage) : (encode message).length = 42 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUIntLE_length]

theorem encode_length_pos (message : OrderMassCancelRequestMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OrderMassCancelRequestMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
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
  rw [Alpha.decode_encode, some_bind]
  rfl

end OrderMassCancelRequestMessage

/-- Transact Time: 8 bytes -/
structure TransactTime where
  seconds : BitVec 32
  nanoseconds : BitVec 32
  deriving DecidableEq, Repr

namespace TransactTime

def encode (message : TransactTime) : List UInt8 :=
  encodeUIntLE 4 message.seconds
    ++ (encodeUIntLE 4 message.nanoseconds)

def decode (bytes : List UInt8) : Option (TransactTime × List UInt8) := do
  let (seconds, bytes) ← decodeUIntLE 4 bytes
  let (nanoseconds, bytes) ← decodeUIntLE 4 bytes
  pure ({ seconds, nanoseconds }, bytes)

@[simp] theorem encode_length (message : TransactTime) : (encode message).length = 8 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length]

theorem encode_length_pos (message : TransactTime) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : TransactTime) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end TransactTime

/-- Execution Report Message: 151 bytes -/
structure ExecutionReportMessage where
  appId : BitVec 8
  sequenceNo : BitVec 32
  executionId : Alpha 12
  clientOrderId : Alpha 20
  orderId : Alpha 12
  execType : ExecType
  executionReportRefId : Alpha 12
  executionReportOrderStatus : BitVec 8
  orderRejectCode : BitVec 32
  executedPrice : BitVec 64
  executedQty : BitVec 32
  leavesQty : BitVec 32
  waiverFlagsPostTradeFlags : BitVec 8
  displayQty : BitVec 32
  instrumentId : BitVec 32
  restatementReason : BitVec 8
  executionReportPeggedExecInst : BitVec 8
  side : BitVec 8
  ownerType : BitVec 8
  reserved7 : Alpha 7
  counterparty : Alpha 11
  tradeLiquidityIndicator : TradeLiquidityIndicator
  tradeMatchId : BitVec 64
  transactTime : TransactTime
  lastMarket : BitVec 8
  typeOfTrade : BitVec 8
  capacity : BitVec 8
  reserved1 : Alpha 1
  publicOrderId : Alpha 12
  minimumQuantity : BitVec 32
  deriving DecidableEq, Repr

namespace ExecutionReportMessage

def encode (message : ExecutionReportMessage) : List UInt8 :=
  encodeUIntLE 1 message.appId
    ++ (encodeUIntLE 4 message.sequenceNo
    ++ (Alpha.encode message.executionId
    ++ (Alpha.encode message.clientOrderId
    ++ (Alpha.encode message.orderId
    ++ (ExecType.encode message.execType
    ++ (Alpha.encode message.executionReportRefId
    ++ (encodeUIntLE 1 message.executionReportOrderStatus
    ++ (encodeUIntLE 4 message.orderRejectCode
    ++ (encodeUIntLE 8 message.executedPrice
    ++ (encodeUIntLE 4 message.executedQty
    ++ (encodeUIntLE 4 message.leavesQty
    ++ (encodeUIntLE 1 message.waiverFlagsPostTradeFlags
    ++ (encodeUIntLE 4 message.displayQty
    ++ (encodeUIntLE 4 message.instrumentId
    ++ (encodeUIntLE 1 message.restatementReason
    ++ (encodeUIntLE 1 message.executionReportPeggedExecInst
    ++ (encodeUIntLE 1 message.side
    ++ (encodeUIntLE 1 message.ownerType
    ++ (Alpha.encode message.reserved7
    ++ (Alpha.encode message.counterparty
    ++ (TradeLiquidityIndicator.encode message.tradeLiquidityIndicator
    ++ (encodeUIntLE 8 message.tradeMatchId
    ++ (TransactTime.encode message.transactTime
    ++ (encodeUIntLE 1 message.lastMarket
    ++ (encodeUIntLE 1 message.typeOfTrade
    ++ (encodeUIntLE 1 message.capacity
    ++ (Alpha.encode message.reserved1
    ++ (Alpha.encode message.publicOrderId
    ++ (encodeUIntLE 4 message.minimumQuantity)))))))))))))))))))))))))))))

-- a long run of fields nests deeper than the elaborator's default limit
set_option maxRecDepth 4096 in
def decode (bytes : List UInt8) : Option (ExecutionReportMessage × List UInt8) := do
  let (appId, bytes) ← decodeUIntLE 1 bytes
  let (sequenceNo, bytes) ← decodeUIntLE 4 bytes
  let (executionId, bytes) ← Alpha.decode 12 bytes
  let (clientOrderId, bytes) ← Alpha.decode 20 bytes
  let (orderId, bytes) ← Alpha.decode 12 bytes
  let (execType, bytes) ← ExecType.decode bytes
  let (executionReportRefId, bytes) ← Alpha.decode 12 bytes
  let (executionReportOrderStatus, bytes) ← decodeUIntLE 1 bytes
  let (orderRejectCode, bytes) ← decodeUIntLE 4 bytes
  let (executedPrice, bytes) ← decodeUIntLE 8 bytes
  let (executedQty, bytes) ← decodeUIntLE 4 bytes
  let (leavesQty, bytes) ← decodeUIntLE 4 bytes
  let (waiverFlagsPostTradeFlags, bytes) ← decodeUIntLE 1 bytes
  let (displayQty, bytes) ← decodeUIntLE 4 bytes
  let (instrumentId, bytes) ← decodeUIntLE 4 bytes
  let (restatementReason, bytes) ← decodeUIntLE 1 bytes
  let (executionReportPeggedExecInst, bytes) ← decodeUIntLE 1 bytes
  let (side, bytes) ← decodeUIntLE 1 bytes
  let (ownerType, bytes) ← decodeUIntLE 1 bytes
  let (reserved7, bytes) ← Alpha.decode 7 bytes
  let (counterparty, bytes) ← Alpha.decode 11 bytes
  let (tradeLiquidityIndicator, bytes) ← TradeLiquidityIndicator.decode bytes
  let (tradeMatchId, bytes) ← decodeUIntLE 8 bytes
  let (transactTime, bytes) ← TransactTime.decode bytes
  let (lastMarket, bytes) ← decodeUIntLE 1 bytes
  let (typeOfTrade, bytes) ← decodeUIntLE 1 bytes
  let (capacity, bytes) ← decodeUIntLE 1 bytes
  let (reserved1, bytes) ← Alpha.decode 1 bytes
  let (publicOrderId, bytes) ← Alpha.decode 12 bytes
  let (minimumQuantity, bytes) ← decodeUIntLE 4 bytes
  pure ({ appId, sequenceNo, executionId, clientOrderId, orderId, execType, executionReportRefId, executionReportOrderStatus, orderRejectCode, executedPrice, executedQty, leavesQty, waiverFlagsPostTradeFlags, displayQty, instrumentId, restatementReason, executionReportPeggedExecInst, side, ownerType, reserved7, counterparty, tradeLiquidityIndicator, tradeMatchId, transactTime, lastMarket, typeOfTrade, capacity, reserved1, publicOrderId, minimumQuantity }, bytes)

@[simp] theorem encode_length (message : ExecutionReportMessage) : (encode message).length = 151 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length, ExecType.encode_length, TradeLiquidityIndicator.encode_length, TransactTime.encode_length]

theorem encode_length_pos (message : ExecutionReportMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

set_option maxRecDepth 4096 in
@[simp] theorem decode_encode (message : ExecutionReportMessage) (rest : List UInt8) :
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
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, ExecType.decode_encode, some_bind]
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
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, TradeLiquidityIndicator.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, TransactTime.decode_encode, some_bind]
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
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end ExecutionReportMessage

/-- Order Cancel Reject Message: 59 bytes -/
structure OrderCancelRejectMessage where
  appId : BitVec 8
  sequenceNo : BitVec 32
  clientOrderId : Alpha 20
  orderId : Alpha 12
  cancelRejectReason : BitVec 32
  transactTime : TransactTime
  rfqId : Alpha 10
  deriving DecidableEq, Repr

namespace OrderCancelRejectMessage

def encode (message : OrderCancelRejectMessage) : List UInt8 :=
  encodeUIntLE 1 message.appId
    ++ (encodeUIntLE 4 message.sequenceNo
    ++ (Alpha.encode message.clientOrderId
    ++ (Alpha.encode message.orderId
    ++ (encodeUIntLE 4 message.cancelRejectReason
    ++ (TransactTime.encode message.transactTime
    ++ (Alpha.encode message.rfqId))))))

def decode (bytes : List UInt8) : Option (OrderCancelRejectMessage × List UInt8) := do
  let (appId, bytes) ← decodeUIntLE 1 bytes
  let (sequenceNo, bytes) ← decodeUIntLE 4 bytes
  let (clientOrderId, bytes) ← Alpha.decode 20 bytes
  let (orderId, bytes) ← Alpha.decode 12 bytes
  let (cancelRejectReason, bytes) ← decodeUIntLE 4 bytes
  let (transactTime, bytes) ← TransactTime.decode bytes
  let (rfqId, bytes) ← Alpha.decode 10 bytes
  pure ({ appId, sequenceNo, clientOrderId, orderId, cancelRejectReason, transactTime, rfqId }, bytes)

@[simp] theorem encode_length (message : OrderCancelRejectMessage) : (encode message).length = 59 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length, TransactTime.encode_length]

theorem encode_length_pos (message : OrderCancelRejectMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OrderCancelRejectMessage) (rest : List UInt8) :
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
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, TransactTime.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end OrderCancelRejectMessage

/-- Order Mass Cancel Report Message: 52 bytes -/
structure OrderMassCancelReportMessage where
  appId : BitVec 8
  sequenceNo : BitVec 32
  clientOrderId : Alpha 20
  massCancelResponse : BitVec 8
  massCancelRejectReason : BitVec 32
  reserved4 : Alpha 4
  transactTime : TransactTime
  reserved10 : Alpha 10
  deriving DecidableEq, Repr

namespace OrderMassCancelReportMessage

def encode (message : OrderMassCancelReportMessage) : List UInt8 :=
  encodeUIntLE 1 message.appId
    ++ (encodeUIntLE 4 message.sequenceNo
    ++ (Alpha.encode message.clientOrderId
    ++ (encodeUIntLE 1 message.massCancelResponse
    ++ (encodeUIntLE 4 message.massCancelRejectReason
    ++ (Alpha.encode message.reserved4
    ++ (TransactTime.encode message.transactTime
    ++ (Alpha.encode message.reserved10)))))))

def decode (bytes : List UInt8) : Option (OrderMassCancelReportMessage × List UInt8) := do
  let (appId, bytes) ← decodeUIntLE 1 bytes
  let (sequenceNo, bytes) ← decodeUIntLE 4 bytes
  let (clientOrderId, bytes) ← Alpha.decode 20 bytes
  let (massCancelResponse, bytes) ← decodeUIntLE 1 bytes
  let (massCancelRejectReason, bytes) ← decodeUIntLE 4 bytes
  let (reserved4, bytes) ← Alpha.decode 4 bytes
  let (transactTime, bytes) ← TransactTime.decode bytes
  let (reserved10, bytes) ← Alpha.decode 10 bytes
  pure ({ appId, sequenceNo, clientOrderId, massCancelResponse, massCancelRejectReason, reserved4, transactTime, reserved10 }, bytes)

@[simp] theorem encode_length (message : OrderMassCancelReportMessage) : (encode message).length = 52 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length, TransactTime.encode_length]

theorem encode_length_pos (message : OrderMassCancelReportMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OrderMassCancelReportMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
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
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, TransactTime.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end OrderMassCancelReportMessage

/-- Quote Request Message: 157 bytes -/
structure QuoteRequestMessage where
  partitionId : BitVec 8
  sequenceNumber : BitVec 32
  quoteReqId : Alpha 10
  orderBook : BitVec 8
  privateQuote : BitVec 8
  instrumentId : BitVec 32
  side : BitVec 8
  orderQuantity : BitVec 32
  expireTime : BitVec 32
  marketMakers : Alpha 60
  contraTrader : Alpha 11
  contraFirm : Alpha 11
  rfqId : Alpha 10
  clientId : BitVec 32
  investmentDecisionMaker : BitVec 32
  executingTrader : BitVec 32
  miFidFlags : BitVec 8
  partyRoleQualifiers : BitVec 8
  quoteRequestType : BitVec 8
  price : BitVec 64
  rfqExecutionDelay : BitVec 8
  rfqMinQuotes : BitVec 8
  accountType : BitVec 8
  orderCapacity : BitVec 8
  rfqDiscloseSide : BitVec 8
  expireTimeMilliseconds : BitVec 32
  autoRfqExecStrategy : BitVec 8
  numOfCompetitors : BitVec 8
  marketMakerRank : BitVec 8
  deriving DecidableEq, Repr

namespace QuoteRequestMessage

def encode (message : QuoteRequestMessage) : List UInt8 :=
  encodeUIntLE 1 message.partitionId
    ++ (encodeUIntLE 4 message.sequenceNumber
    ++ (Alpha.encode message.quoteReqId
    ++ (encodeUIntLE 1 message.orderBook
    ++ (encodeUIntLE 1 message.privateQuote
    ++ (encodeUIntLE 4 message.instrumentId
    ++ (encodeUIntLE 1 message.side
    ++ (encodeUIntLE 4 message.orderQuantity
    ++ (encodeUIntLE 4 message.expireTime
    ++ (Alpha.encode message.marketMakers
    ++ (Alpha.encode message.contraTrader
    ++ (Alpha.encode message.contraFirm
    ++ (Alpha.encode message.rfqId
    ++ (encodeUIntLE 4 message.clientId
    ++ (encodeUIntLE 4 message.investmentDecisionMaker
    ++ (encodeUIntLE 4 message.executingTrader
    ++ (encodeUIntLE 1 message.miFidFlags
    ++ (encodeUIntLE 1 message.partyRoleQualifiers
    ++ (encodeUIntLE 1 message.quoteRequestType
    ++ (encodeUIntLE 8 message.price
    ++ (encodeUIntLE 1 message.rfqExecutionDelay
    ++ (encodeUIntLE 1 message.rfqMinQuotes
    ++ (encodeUIntLE 1 message.accountType
    ++ (encodeUIntLE 1 message.orderCapacity
    ++ (encodeUIntLE 1 message.rfqDiscloseSide
    ++ (encodeUIntLE 4 message.expireTimeMilliseconds
    ++ (encodeUIntLE 1 message.autoRfqExecStrategy
    ++ (encodeUIntLE 1 message.numOfCompetitors
    ++ (encodeUIntLE 1 message.marketMakerRank))))))))))))))))))))))))))))

-- a long run of fields nests deeper than the elaborator's default limit
set_option maxRecDepth 4096 in
def decode (bytes : List UInt8) : Option (QuoteRequestMessage × List UInt8) := do
  let (partitionId, bytes) ← decodeUIntLE 1 bytes
  let (sequenceNumber, bytes) ← decodeUIntLE 4 bytes
  let (quoteReqId, bytes) ← Alpha.decode 10 bytes
  let (orderBook, bytes) ← decodeUIntLE 1 bytes
  let (privateQuote, bytes) ← decodeUIntLE 1 bytes
  let (instrumentId, bytes) ← decodeUIntLE 4 bytes
  let (side, bytes) ← decodeUIntLE 1 bytes
  let (orderQuantity, bytes) ← decodeUIntLE 4 bytes
  let (expireTime, bytes) ← decodeUIntLE 4 bytes
  let (marketMakers, bytes) ← Alpha.decode 60 bytes
  let (contraTrader, bytes) ← Alpha.decode 11 bytes
  let (contraFirm, bytes) ← Alpha.decode 11 bytes
  let (rfqId, bytes) ← Alpha.decode 10 bytes
  let (clientId, bytes) ← decodeUIntLE 4 bytes
  let (investmentDecisionMaker, bytes) ← decodeUIntLE 4 bytes
  let (executingTrader, bytes) ← decodeUIntLE 4 bytes
  let (miFidFlags, bytes) ← decodeUIntLE 1 bytes
  let (partyRoleQualifiers, bytes) ← decodeUIntLE 1 bytes
  let (quoteRequestType, bytes) ← decodeUIntLE 1 bytes
  let (price, bytes) ← decodeUIntLE 8 bytes
  let (rfqExecutionDelay, bytes) ← decodeUIntLE 1 bytes
  let (rfqMinQuotes, bytes) ← decodeUIntLE 1 bytes
  let (accountType, bytes) ← decodeUIntLE 1 bytes
  let (orderCapacity, bytes) ← decodeUIntLE 1 bytes
  let (rfqDiscloseSide, bytes) ← decodeUIntLE 1 bytes
  let (expireTimeMilliseconds, bytes) ← decodeUIntLE 4 bytes
  let (autoRfqExecStrategy, bytes) ← decodeUIntLE 1 bytes
  let (numOfCompetitors, bytes) ← decodeUIntLE 1 bytes
  let (marketMakerRank, bytes) ← decodeUIntLE 1 bytes
  pure ({ partitionId, sequenceNumber, quoteReqId, orderBook, privateQuote, instrumentId, side, orderQuantity, expireTime, marketMakers, contraTrader, contraFirm, rfqId, clientId, investmentDecisionMaker, executingTrader, miFidFlags, partyRoleQualifiers, quoteRequestType, price, rfqExecutionDelay, rfqMinQuotes, accountType, orderCapacity, rfqDiscloseSide, expireTimeMilliseconds, autoRfqExecStrategy, numOfCompetitors, marketMakerRank }, bytes)

@[simp] theorem encode_length (message : QuoteRequestMessage) : (encode message).length = 157 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length]

theorem encode_length_pos (message : QuoteRequestMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

set_option maxRecDepth 4096 in
@[simp] theorem decode_encode (message : QuoteRequestMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
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
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end QuoteRequestMessage

/-- Quote Status Report Message: 143 bytes -/
structure QuoteStatusReportMessage where
  partitionId : BitVec 8
  sequenceNumber : BitVec 32
  quoteMsgId : Alpha 20
  quoteReqId : Alpha 10
  quoteStatus : BitVec 8
  rejectCode : BitVec 32
  orderBook : BitVec 8
  marketMakers : Alpha 60
  rfqId : Alpha 10
  expireTime : BitVec 32
  bidId : Alpha 12
  offerId : Alpha 12
  expireTimeMilliseconds : BitVec 32
  deriving DecidableEq, Repr

namespace QuoteStatusReportMessage

def encode (message : QuoteStatusReportMessage) : List UInt8 :=
  encodeUIntLE 1 message.partitionId
    ++ (encodeUIntLE 4 message.sequenceNumber
    ++ (Alpha.encode message.quoteMsgId
    ++ (Alpha.encode message.quoteReqId
    ++ (encodeUIntLE 1 message.quoteStatus
    ++ (encodeUIntLE 4 message.rejectCode
    ++ (encodeUIntLE 1 message.orderBook
    ++ (Alpha.encode message.marketMakers
    ++ (Alpha.encode message.rfqId
    ++ (encodeUIntLE 4 message.expireTime
    ++ (Alpha.encode message.bidId
    ++ (Alpha.encode message.offerId
    ++ (encodeUIntLE 4 message.expireTimeMilliseconds))))))))))))

def decode (bytes : List UInt8) : Option (QuoteStatusReportMessage × List UInt8) := do
  let (partitionId, bytes) ← decodeUIntLE 1 bytes
  let (sequenceNumber, bytes) ← decodeUIntLE 4 bytes
  let (quoteMsgId, bytes) ← Alpha.decode 20 bytes
  let (quoteReqId, bytes) ← Alpha.decode 10 bytes
  let (quoteStatus, bytes) ← decodeUIntLE 1 bytes
  let (rejectCode, bytes) ← decodeUIntLE 4 bytes
  let (orderBook, bytes) ← decodeUIntLE 1 bytes
  let (marketMakers, bytes) ← Alpha.decode 60 bytes
  let (rfqId, bytes) ← Alpha.decode 10 bytes
  let (expireTime, bytes) ← decodeUIntLE 4 bytes
  let (bidId, bytes) ← Alpha.decode 12 bytes
  let (offerId, bytes) ← Alpha.decode 12 bytes
  let (expireTimeMilliseconds, bytes) ← decodeUIntLE 4 bytes
  pure ({ partitionId, sequenceNumber, quoteMsgId, quoteReqId, quoteStatus, rejectCode, orderBook, marketMakers, rfqId, expireTime, bidId, offerId, expireTimeMilliseconds }, bytes)

@[simp] theorem encode_length (message : QuoteStatusReportMessage) : (encode message).length = 143 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length]

theorem encode_length_pos (message : QuoteStatusReportMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : QuoteStatusReportMessage) (rest : List UInt8) :
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
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end QuoteStatusReportMessage

/-- Quote Request Reject Message: 110 bytes -/
structure QuoteRequestRejectMessage where
  partitionId : BitVec 8
  sequenceNumber : BitVec 32
  quoteReqId : Alpha 10
  rejectCode : BitVec 32
  orderBook : BitVec 8
  instrumentId : BitVec 32
  side : BitVec 8
  orderQuantity : BitVec 32
  marketMakers : Alpha 60
  contraTrader : Alpha 11
  rfqId : Alpha 10
  deriving DecidableEq, Repr

namespace QuoteRequestRejectMessage

def encode (message : QuoteRequestRejectMessage) : List UInt8 :=
  encodeUIntLE 1 message.partitionId
    ++ (encodeUIntLE 4 message.sequenceNumber
    ++ (Alpha.encode message.quoteReqId
    ++ (encodeUIntLE 4 message.rejectCode
    ++ (encodeUIntLE 1 message.orderBook
    ++ (encodeUIntLE 4 message.instrumentId
    ++ (encodeUIntLE 1 message.side
    ++ (encodeUIntLE 4 message.orderQuantity
    ++ (Alpha.encode message.marketMakers
    ++ (Alpha.encode message.contraTrader
    ++ (Alpha.encode message.rfqId))))))))))

def decode (bytes : List UInt8) : Option (QuoteRequestRejectMessage × List UInt8) := do
  let (partitionId, bytes) ← decodeUIntLE 1 bytes
  let (sequenceNumber, bytes) ← decodeUIntLE 4 bytes
  let (quoteReqId, bytes) ← Alpha.decode 10 bytes
  let (rejectCode, bytes) ← decodeUIntLE 4 bytes
  let (orderBook, bytes) ← decodeUIntLE 1 bytes
  let (instrumentId, bytes) ← decodeUIntLE 4 bytes
  let (side, bytes) ← decodeUIntLE 1 bytes
  let (orderQuantity, bytes) ← decodeUIntLE 4 bytes
  let (marketMakers, bytes) ← Alpha.decode 60 bytes
  let (contraTrader, bytes) ← Alpha.decode 11 bytes
  let (rfqId, bytes) ← Alpha.decode 10 bytes
  pure ({ partitionId, sequenceNumber, quoteReqId, rejectCode, orderBook, instrumentId, side, orderQuantity, marketMakers, contraTrader, rfqId }, bytes)

@[simp] theorem encode_length (message : QuoteRequestRejectMessage) : (encode message).length = 110 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length]

theorem encode_length_pos (message : QuoteRequestRejectMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : QuoteRequestRejectMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
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

end QuoteRequestRejectMessage

/-- Rfq Quote Message: 126 bytes -/
structure RfqQuoteMessage where
  partitionId : BitVec 8
  sequenceNumber : BitVec 32
  quoteMsgId : Alpha 20
  rfqId : Alpha 10
  instrumentId : BitVec 32
  bidPrice : BitVec 64
  bidQuantity : BitVec 32
  offerPrice : BitVec 64
  offerQuantity : BitVec 32
  autoCancel : BitVec 8
  marketMaker : Alpha 11
  marketMakerFirm : Alpha 11
  bidId : Alpha 12
  offerId : Alpha 12
  capacity : BitVec 8
  clearingAccount : BitVec 8
  clientId : BitVec 32
  investmentDecisionMaker : BitVec 32
  executingTrader : BitVec 32
  miFidFlags : BitVec 8
  partyRoleQualifiers : BitVec 8
  deriving DecidableEq, Repr

namespace RfqQuoteMessage

def encode (message : RfqQuoteMessage) : List UInt8 :=
  encodeUIntLE 1 message.partitionId
    ++ (encodeUIntLE 4 message.sequenceNumber
    ++ (Alpha.encode message.quoteMsgId
    ++ (Alpha.encode message.rfqId
    ++ (encodeUIntLE 4 message.instrumentId
    ++ (encodeUIntLE 8 message.bidPrice
    ++ (encodeUIntLE 4 message.bidQuantity
    ++ (encodeUIntLE 8 message.offerPrice
    ++ (encodeUIntLE 4 message.offerQuantity
    ++ (encodeUIntLE 1 message.autoCancel
    ++ (Alpha.encode message.marketMaker
    ++ (Alpha.encode message.marketMakerFirm
    ++ (Alpha.encode message.bidId
    ++ (Alpha.encode message.offerId
    ++ (encodeUIntLE 1 message.capacity
    ++ (encodeUIntLE 1 message.clearingAccount
    ++ (encodeUIntLE 4 message.clientId
    ++ (encodeUIntLE 4 message.investmentDecisionMaker
    ++ (encodeUIntLE 4 message.executingTrader
    ++ (encodeUIntLE 1 message.miFidFlags
    ++ (encodeUIntLE 1 message.partyRoleQualifiers))))))))))))))))))))

def decode (bytes : List UInt8) : Option (RfqQuoteMessage × List UInt8) := do
  let (partitionId, bytes) ← decodeUIntLE 1 bytes
  let (sequenceNumber, bytes) ← decodeUIntLE 4 bytes
  let (quoteMsgId, bytes) ← Alpha.decode 20 bytes
  let (rfqId, bytes) ← Alpha.decode 10 bytes
  let (instrumentId, bytes) ← decodeUIntLE 4 bytes
  let (bidPrice, bytes) ← decodeUIntLE 8 bytes
  let (bidQuantity, bytes) ← decodeUIntLE 4 bytes
  let (offerPrice, bytes) ← decodeUIntLE 8 bytes
  let (offerQuantity, bytes) ← decodeUIntLE 4 bytes
  let (autoCancel, bytes) ← decodeUIntLE 1 bytes
  let (marketMaker, bytes) ← Alpha.decode 11 bytes
  let (marketMakerFirm, bytes) ← Alpha.decode 11 bytes
  let (bidId, bytes) ← Alpha.decode 12 bytes
  let (offerId, bytes) ← Alpha.decode 12 bytes
  let (capacity, bytes) ← decodeUIntLE 1 bytes
  let (clearingAccount, bytes) ← decodeUIntLE 1 bytes
  let (clientId, bytes) ← decodeUIntLE 4 bytes
  let (investmentDecisionMaker, bytes) ← decodeUIntLE 4 bytes
  let (executingTrader, bytes) ← decodeUIntLE 4 bytes
  let (miFidFlags, bytes) ← decodeUIntLE 1 bytes
  let (partyRoleQualifiers, bytes) ← decodeUIntLE 1 bytes
  pure ({ partitionId, sequenceNumber, quoteMsgId, rfqId, instrumentId, bidPrice, bidQuantity, offerPrice, offerQuantity, autoCancel, marketMaker, marketMakerFirm, bidId, offerId, capacity, clearingAccount, clientId, investmentDecisionMaker, executingTrader, miFidFlags, partyRoleQualifiers }, bytes)

@[simp] theorem encode_length (message : RfqQuoteMessage) : (encode message).length = 126 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length]

theorem encode_length_pos (message : RfqQuoteMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : RfqQuoteMessage) (rest : List UInt8) :
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
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end RfqQuoteMessage

/-- Quote Ack Message: 65 bytes -/
structure QuoteAckMessage where
  partitionId : BitVec 8
  sequenceNumber : BitVec 32
  quoteMsgId : Alpha 20
  rfqId : Alpha 10
  bidId : Alpha 12
  offerId : Alpha 12
  quoteAckStatus : BitVec 8
  rejectCode : BitVec 32
  orderBook : BitVec 8
  deriving DecidableEq, Repr

namespace QuoteAckMessage

def encode (message : QuoteAckMessage) : List UInt8 :=
  encodeUIntLE 1 message.partitionId
    ++ (encodeUIntLE 4 message.sequenceNumber
    ++ (Alpha.encode message.quoteMsgId
    ++ (Alpha.encode message.rfqId
    ++ (Alpha.encode message.bidId
    ++ (Alpha.encode message.offerId
    ++ (encodeUIntLE 1 message.quoteAckStatus
    ++ (encodeUIntLE 4 message.rejectCode
    ++ (encodeUIntLE 1 message.orderBook))))))))

def decode (bytes : List UInt8) : Option (QuoteAckMessage × List UInt8) := do
  let (partitionId, bytes) ← decodeUIntLE 1 bytes
  let (sequenceNumber, bytes) ← decodeUIntLE 4 bytes
  let (quoteMsgId, bytes) ← Alpha.decode 20 bytes
  let (rfqId, bytes) ← Alpha.decode 10 bytes
  let (bidId, bytes) ← Alpha.decode 12 bytes
  let (offerId, bytes) ← Alpha.decode 12 bytes
  let (quoteAckStatus, bytes) ← decodeUIntLE 1 bytes
  let (rejectCode, bytes) ← decodeUIntLE 4 bytes
  let (orderBook, bytes) ← decodeUIntLE 1 bytes
  pure ({ partitionId, sequenceNumber, quoteMsgId, rfqId, bidId, offerId, quoteAckStatus, rejectCode, orderBook }, bytes)

@[simp] theorem encode_length (message : QuoteAckMessage) : (encode message).length = 65 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length]

theorem encode_length_pos (message : QuoteAckMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : QuoteAckMessage) (rest : List UInt8) :
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
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end QuoteAckMessage

/-- Quote Response Message: 88 bytes -/
structure QuoteResponseMessage where
  partitionId : BitVec 8
  sequenceNumber : BitVec 32
  quoteMsgId : Alpha 20
  rfqId : Alpha 10
  quoteRespType : BitVec 8
  instrumentId : BitVec 32
  side : BitVec 8
  orderQuantity : BitVec 32
  limitPrice : BitVec 64
  orderBook : BitVec 8
  bidId : Alpha 12
  offerId : Alpha 12
  capacity : BitVec 8
  clearingAccount : BitVec 8
  reserved8 : Alpha 8
  deriving DecidableEq, Repr

namespace QuoteResponseMessage

def encode (message : QuoteResponseMessage) : List UInt8 :=
  encodeUIntLE 1 message.partitionId
    ++ (encodeUIntLE 4 message.sequenceNumber
    ++ (Alpha.encode message.quoteMsgId
    ++ (Alpha.encode message.rfqId
    ++ (encodeUIntLE 1 message.quoteRespType
    ++ (encodeUIntLE 4 message.instrumentId
    ++ (encodeUIntLE 1 message.side
    ++ (encodeUIntLE 4 message.orderQuantity
    ++ (encodeUIntLE 8 message.limitPrice
    ++ (encodeUIntLE 1 message.orderBook
    ++ (Alpha.encode message.bidId
    ++ (Alpha.encode message.offerId
    ++ (encodeUIntLE 1 message.capacity
    ++ (encodeUIntLE 1 message.clearingAccount
    ++ (Alpha.encode message.reserved8))))))))))))))

def decode (bytes : List UInt8) : Option (QuoteResponseMessage × List UInt8) := do
  let (partitionId, bytes) ← decodeUIntLE 1 bytes
  let (sequenceNumber, bytes) ← decodeUIntLE 4 bytes
  let (quoteMsgId, bytes) ← Alpha.decode 20 bytes
  let (rfqId, bytes) ← Alpha.decode 10 bytes
  let (quoteRespType, bytes) ← decodeUIntLE 1 bytes
  let (instrumentId, bytes) ← decodeUIntLE 4 bytes
  let (side, bytes) ← decodeUIntLE 1 bytes
  let (orderQuantity, bytes) ← decodeUIntLE 4 bytes
  let (limitPrice, bytes) ← decodeUIntLE 8 bytes
  let (orderBook, bytes) ← decodeUIntLE 1 bytes
  let (bidId, bytes) ← Alpha.decode 12 bytes
  let (offerId, bytes) ← Alpha.decode 12 bytes
  let (capacity, bytes) ← decodeUIntLE 1 bytes
  let (clearingAccount, bytes) ← decodeUIntLE 1 bytes
  let (reserved8, bytes) ← Alpha.decode 8 bytes
  pure ({ partitionId, sequenceNumber, quoteMsgId, rfqId, quoteRespType, instrumentId, side, orderQuantity, limitPrice, orderBook, bidId, offerId, capacity, clearingAccount, reserved8 }, bytes)

@[simp] theorem encode_length (message : QuoteResponseMessage) : (encode message).length = 88 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length]

theorem encode_length_pos (message : QuoteResponseMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : QuoteResponseMessage) (rest : List UInt8) :
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

end QuoteResponseMessage

/-- Rfq Execution Report Message: 153 bytes -/
structure RfqExecutionReportMessage where
  partitionId : BitVec 8
  sequenceNumber : BitVec 32
  executionId : Alpha 12
  rfqId : Alpha 10
  orderId : Alpha 12
  executionType : ExecutionType
  tradeMatchId : BitVec 64
  side : BitVec 8
  executedQuantity : BitVec 32
  executedPrice : BitVec 64
  transactTime : TransactTime
  reserved8 : Alpha 8
  secondReserved8 : Alpha 8
  rfqExecutionReportOrderStatus : BitVec 8
  leavesQuantity : BitVec 32
  instrumentId : BitVec 32
  thirdReserved8 : Alpha 8
  fourthReserved8 : Alpha 8
  contraFirm : Alpha 11
  capacity : BitVec 8
  clearingAccount : BitVec 8
  waiverFlags : BitVec 8
  executionReportRefId : Alpha 12
  contraOrderBook : BitVec 8
  avgPx : BitVec 64
  lastMarket : BitVec 8
  reserved7 : Alpha 7
  deriving DecidableEq, Repr

namespace RfqExecutionReportMessage

def encode (message : RfqExecutionReportMessage) : List UInt8 :=
  encodeUIntLE 1 message.partitionId
    ++ (encodeUIntLE 4 message.sequenceNumber
    ++ (Alpha.encode message.executionId
    ++ (Alpha.encode message.rfqId
    ++ (Alpha.encode message.orderId
    ++ (ExecutionType.encode message.executionType
    ++ (encodeUIntLE 8 message.tradeMatchId
    ++ (encodeUIntLE 1 message.side
    ++ (encodeUIntLE 4 message.executedQuantity
    ++ (encodeUIntLE 8 message.executedPrice
    ++ (TransactTime.encode message.transactTime
    ++ (Alpha.encode message.reserved8
    ++ (Alpha.encode message.secondReserved8
    ++ (encodeUIntLE 1 message.rfqExecutionReportOrderStatus
    ++ (encodeUIntLE 4 message.leavesQuantity
    ++ (encodeUIntLE 4 message.instrumentId
    ++ (Alpha.encode message.thirdReserved8
    ++ (Alpha.encode message.fourthReserved8
    ++ (Alpha.encode message.contraFirm
    ++ (encodeUIntLE 1 message.capacity
    ++ (encodeUIntLE 1 message.clearingAccount
    ++ (encodeUIntLE 1 message.waiverFlags
    ++ (Alpha.encode message.executionReportRefId
    ++ (encodeUIntLE 1 message.contraOrderBook
    ++ (encodeUIntLE 8 message.avgPx
    ++ (encodeUIntLE 1 message.lastMarket
    ++ (Alpha.encode message.reserved7))))))))))))))))))))))))))

-- a long run of fields nests deeper than the elaborator's default limit
set_option maxRecDepth 4096 in
def decode (bytes : List UInt8) : Option (RfqExecutionReportMessage × List UInt8) := do
  let (partitionId, bytes) ← decodeUIntLE 1 bytes
  let (sequenceNumber, bytes) ← decodeUIntLE 4 bytes
  let (executionId, bytes) ← Alpha.decode 12 bytes
  let (rfqId, bytes) ← Alpha.decode 10 bytes
  let (orderId, bytes) ← Alpha.decode 12 bytes
  let (executionType, bytes) ← ExecutionType.decode bytes
  let (tradeMatchId, bytes) ← decodeUIntLE 8 bytes
  let (side, bytes) ← decodeUIntLE 1 bytes
  let (executedQuantity, bytes) ← decodeUIntLE 4 bytes
  let (executedPrice, bytes) ← decodeUIntLE 8 bytes
  let (transactTime, bytes) ← TransactTime.decode bytes
  let (reserved8, bytes) ← Alpha.decode 8 bytes
  let (secondReserved8, bytes) ← Alpha.decode 8 bytes
  let (rfqExecutionReportOrderStatus, bytes) ← decodeUIntLE 1 bytes
  let (leavesQuantity, bytes) ← decodeUIntLE 4 bytes
  let (instrumentId, bytes) ← decodeUIntLE 4 bytes
  let (thirdReserved8, bytes) ← Alpha.decode 8 bytes
  let (fourthReserved8, bytes) ← Alpha.decode 8 bytes
  let (contraFirm, bytes) ← Alpha.decode 11 bytes
  let (capacity, bytes) ← decodeUIntLE 1 bytes
  let (clearingAccount, bytes) ← decodeUIntLE 1 bytes
  let (waiverFlags, bytes) ← decodeUIntLE 1 bytes
  let (executionReportRefId, bytes) ← Alpha.decode 12 bytes
  let (contraOrderBook, bytes) ← decodeUIntLE 1 bytes
  let (avgPx, bytes) ← decodeUIntLE 8 bytes
  let (lastMarket, bytes) ← decodeUIntLE 1 bytes
  let (reserved7, bytes) ← Alpha.decode 7 bytes
  pure ({ partitionId, sequenceNumber, executionId, rfqId, orderId, executionType, tradeMatchId, side, executedQuantity, executedPrice, transactTime, reserved8, secondReserved8, rfqExecutionReportOrderStatus, leavesQuantity, instrumentId, thirdReserved8, fourthReserved8, contraFirm, capacity, clearingAccount, waiverFlags, executionReportRefId, contraOrderBook, avgPx, lastMarket, reserved7 }, bytes)

@[simp] theorem encode_length (message : RfqExecutionReportMessage) : (encode message).length = 153 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length, ExecutionType.encode_length, TransactTime.encode_length]

theorem encode_length_pos (message : RfqExecutionReportMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

set_option maxRecDepth 4096 in
@[simp] theorem decode_encode (message : RfqExecutionReportMessage) (rest : List UInt8) :
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
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, ExecutionType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, TransactTime.decode_encode, some_bind]
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
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end RfqExecutionReportMessage

/-- Business Reject Message: 59 bytes -/
structure BusinessRejectMessage where
  appId : BitVec 8
  sequenceNo : BitVec 32
  rejectCode : BitVec 32
  clientOrderId : Alpha 20
  orderId : Alpha 12
  transactTime : TransactTime
  reserved10 : Alpha 10
  deriving DecidableEq, Repr

namespace BusinessRejectMessage

def encode (message : BusinessRejectMessage) : List UInt8 :=
  encodeUIntLE 1 message.appId
    ++ (encodeUIntLE 4 message.sequenceNo
    ++ (encodeUIntLE 4 message.rejectCode
    ++ (Alpha.encode message.clientOrderId
    ++ (Alpha.encode message.orderId
    ++ (TransactTime.encode message.transactTime
    ++ (Alpha.encode message.reserved10))))))

def decode (bytes : List UInt8) : Option (BusinessRejectMessage × List UInt8) := do
  let (appId, bytes) ← decodeUIntLE 1 bytes
  let (sequenceNo, bytes) ← decodeUIntLE 4 bytes
  let (rejectCode, bytes) ← decodeUIntLE 4 bytes
  let (clientOrderId, bytes) ← Alpha.decode 20 bytes
  let (orderId, bytes) ← Alpha.decode 12 bytes
  let (transactTime, bytes) ← TransactTime.decode bytes
  let (reserved10, bytes) ← Alpha.decode 10 bytes
  pure ({ appId, sequenceNo, rejectCode, clientOrderId, orderId, transactTime, reserved10 }, bytes)

@[simp] theorem encode_length (message : BusinessRejectMessage) : (encode message).length = 59 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length, TransactTime.encode_length]

theorem encode_length_pos (message : BusinessRejectMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : BusinessRejectMessage) (rest : List UInt8) :
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
  rw [List.append_assoc, TransactTime.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end BusinessRejectMessage

/-- Any Payload, selected by Message Type -/
inductive Payload where
  | logonMessage (message : LogonMessage) -- "A" 0x41
  | logonReplyMessage (message : LogonReplyMessage) -- "B" 0x42
  | logoutMessage (message : LogoutMessage) -- "5" 0x35
  | heartbeatMessage (message : HeartbeatMessage) -- "0" 0x30
  | rejectMessage (message : RejectMessage) -- "3" 0x33
  | systemStatusMessage (message : SystemStatusMessage) -- "n" 0x6E
  | newOrderMessage (message : NewOrderMessage) -- "D" 0x44
  | newQuoteMessage (message : NewQuoteMessage) -- "S" 0x53
  | orderCancelReplaceRequestMessage (message : OrderCancelReplaceRequestMessage) -- "G" 0x47
  | orderCancelRequestMessage (message : OrderCancelRequestMessage) -- "F" 0x46
  | orderMassCancelRequestMessage (message : OrderMassCancelRequestMessage) -- "q" 0x71
  | executionReportMessage (message : ExecutionReportMessage) -- "8" 0x38
  | orderCancelRejectMessage (message : OrderCancelRejectMessage) -- "9" 0x39
  | orderMassCancelReportMessage (message : OrderMassCancelReportMessage) -- "r" 0x72
  | quoteRequestMessage (message : QuoteRequestMessage) -- "a" 0x61
  | quoteStatusReportMessage (message : QuoteStatusReportMessage) -- "c" 0x63
  | quoteRequestRejectMessage (message : QuoteRequestRejectMessage) -- "b" 0x62
  | rfqQuoteMessage (message : RfqQuoteMessage) -- "d" 0x64
  | quoteAckMessage (message : QuoteAckMessage) -- "e" 0x65
  | quoteResponseMessage (message : QuoteResponseMessage) -- "f" 0x66
  | rfqExecutionReportMessage (message : RfqExecutionReportMessage) -- "g" 0x67
  | businessRejectMessage (message : BusinessRejectMessage) -- "j" 0x6A
  deriving DecidableEq, Repr

namespace Payload

/-- The Message Type each message is sent under -/
def tag : Payload → BitVec 8
  | .logonMessage _ => 65
  | .logonReplyMessage _ => 66
  | .logoutMessage _ => 53
  | .heartbeatMessage _ => 48
  | .rejectMessage _ => 51
  | .systemStatusMessage _ => 110
  | .newOrderMessage _ => 68
  | .newQuoteMessage _ => 83
  | .orderCancelReplaceRequestMessage _ => 71
  | .orderCancelRequestMessage _ => 70
  | .orderMassCancelRequestMessage _ => 113
  | .executionReportMessage _ => 56
  | .orderCancelRejectMessage _ => 57
  | .orderMassCancelReportMessage _ => 114
  | .quoteRequestMessage _ => 97
  | .quoteStatusReportMessage _ => 99
  | .quoteRequestRejectMessage _ => 98
  | .rfqQuoteMessage _ => 100
  | .quoteAckMessage _ => 101
  | .quoteResponseMessage _ => 102
  | .rfqExecutionReportMessage _ => 103
  | .businessRejectMessage _ => 106

def encode : Payload → List UInt8
  | .logonMessage message => LogonMessage.encode message
  | .logonReplyMessage message => LogonReplyMessage.encode message
  | .logoutMessage message => LogoutMessage.encode message
  | .heartbeatMessage message => HeartbeatMessage.encode message
  | .rejectMessage message => RejectMessage.encode message
  | .systemStatusMessage message => SystemStatusMessage.encode message
  | .newOrderMessage message => NewOrderMessage.encode message
  | .newQuoteMessage message => NewQuoteMessage.encode message
  | .orderCancelReplaceRequestMessage message => OrderCancelReplaceRequestMessage.encode message
  | .orderCancelRequestMessage message => OrderCancelRequestMessage.encode message
  | .orderMassCancelRequestMessage message => OrderMassCancelRequestMessage.encode message
  | .executionReportMessage message => ExecutionReportMessage.encode message
  | .orderCancelRejectMessage message => OrderCancelRejectMessage.encode message
  | .orderMassCancelReportMessage message => OrderMassCancelReportMessage.encode message
  | .quoteRequestMessage message => QuoteRequestMessage.encode message
  | .quoteStatusReportMessage message => QuoteStatusReportMessage.encode message
  | .quoteRequestRejectMessage message => QuoteRequestRejectMessage.encode message
  | .rfqQuoteMessage message => RfqQuoteMessage.encode message
  | .quoteAckMessage message => QuoteAckMessage.encode message
  | .quoteResponseMessage message => QuoteResponseMessage.encode message
  | .rfqExecutionReportMessage message => RfqExecutionReportMessage.encode message
  | .businessRejectMessage message => BusinessRejectMessage.encode message

/-- The most bytes any message's encoding can take -/
theorem encode_length_le (message : Payload) : (encode message).length ≤ 157 := by
  cases message with
  | logonMessage inner =>
    simp only [encode, LogonMessage.encode_length]
    omega
  | logonReplyMessage inner =>
    simp only [encode, LogonReplyMessage.encode_length]
    omega
  | logoutMessage inner =>
    simp only [encode, LogoutMessage.encode_length]
    omega
  | heartbeatMessage inner =>
    simp only [encode, HeartbeatMessage.encode_length]
    omega
  | rejectMessage inner =>
    simp only [encode, RejectMessage.encode_length]
    omega
  | systemStatusMessage inner =>
    simp only [encode, SystemStatusMessage.encode_length]
    omega
  | newOrderMessage inner =>
    simp only [encode, NewOrderMessage.encode_length]
    omega
  | newQuoteMessage inner =>
    simp only [encode, NewQuoteMessage.encode_length]
    omega
  | orderCancelReplaceRequestMessage inner =>
    simp only [encode, OrderCancelReplaceRequestMessage.encode_length]
    omega
  | orderCancelRequestMessage inner =>
    simp only [encode, OrderCancelRequestMessage.encode_length]
    omega
  | orderMassCancelRequestMessage inner =>
    simp only [encode, OrderMassCancelRequestMessage.encode_length]
    omega
  | executionReportMessage inner =>
    simp only [encode, ExecutionReportMessage.encode_length]
    omega
  | orderCancelRejectMessage inner =>
    simp only [encode, OrderCancelRejectMessage.encode_length]
    omega
  | orderMassCancelReportMessage inner =>
    simp only [encode, OrderMassCancelReportMessage.encode_length]
    omega
  | quoteRequestMessage inner =>
    simp only [encode, QuoteRequestMessage.encode_length]
    omega
  | quoteStatusReportMessage inner =>
    simp only [encode, QuoteStatusReportMessage.encode_length]
    omega
  | quoteRequestRejectMessage inner =>
    simp only [encode, QuoteRequestRejectMessage.encode_length]
    omega
  | rfqQuoteMessage inner =>
    simp only [encode, RfqQuoteMessage.encode_length]
    omega
  | quoteAckMessage inner =>
    simp only [encode, QuoteAckMessage.encode_length]
    omega
  | quoteResponseMessage inner =>
    simp only [encode, QuoteResponseMessage.encode_length]
    omega
  | rfqExecutionReportMessage inner =>
    simp only [encode, RfqExecutionReportMessage.encode_length]
    omega
  | businessRejectMessage inner =>
    simp only [encode, BusinessRejectMessage.encode_length]
    omega

def decode (tag : BitVec 8) (bytes : List UInt8) : Option (Payload × List UInt8) :=
  if tag = 65 then (LogonMessage.decode bytes).map fun (message, rest) => (.logonMessage message, rest)
  else if tag = 66 then (LogonReplyMessage.decode bytes).map fun (message, rest) => (.logonReplyMessage message, rest)
  else if tag = 53 then (LogoutMessage.decode bytes).map fun (message, rest) => (.logoutMessage message, rest)
  else if tag = 48 then (HeartbeatMessage.decode bytes).map fun (message, rest) => (.heartbeatMessage message, rest)
  else if tag = 51 then (RejectMessage.decode bytes).map fun (message, rest) => (.rejectMessage message, rest)
  else if tag = 110 then (SystemStatusMessage.decode bytes).map fun (message, rest) => (.systemStatusMessage message, rest)
  else if tag = 68 then (NewOrderMessage.decode bytes).map fun (message, rest) => (.newOrderMessage message, rest)
  else if tag = 83 then (NewQuoteMessage.decode bytes).map fun (message, rest) => (.newQuoteMessage message, rest)
  else if tag = 71 then (OrderCancelReplaceRequestMessage.decode bytes).map fun (message, rest) => (.orderCancelReplaceRequestMessage message, rest)
  else if tag = 70 then (OrderCancelRequestMessage.decode bytes).map fun (message, rest) => (.orderCancelRequestMessage message, rest)
  else if tag = 113 then (OrderMassCancelRequestMessage.decode bytes).map fun (message, rest) => (.orderMassCancelRequestMessage message, rest)
  else if tag = 56 then (ExecutionReportMessage.decode bytes).map fun (message, rest) => (.executionReportMessage message, rest)
  else if tag = 57 then (OrderCancelRejectMessage.decode bytes).map fun (message, rest) => (.orderCancelRejectMessage message, rest)
  else if tag = 114 then (OrderMassCancelReportMessage.decode bytes).map fun (message, rest) => (.orderMassCancelReportMessage message, rest)
  else if tag = 97 then (QuoteRequestMessage.decode bytes).map fun (message, rest) => (.quoteRequestMessage message, rest)
  else if tag = 99 then (QuoteStatusReportMessage.decode bytes).map fun (message, rest) => (.quoteStatusReportMessage message, rest)
  else if tag = 98 then (QuoteRequestRejectMessage.decode bytes).map fun (message, rest) => (.quoteRequestRejectMessage message, rest)
  else if tag = 100 then (RfqQuoteMessage.decode bytes).map fun (message, rest) => (.rfqQuoteMessage message, rest)
  else if tag = 101 then (QuoteAckMessage.decode bytes).map fun (message, rest) => (.quoteAckMessage message, rest)
  else if tag = 102 then (QuoteResponseMessage.decode bytes).map fun (message, rest) => (.quoteResponseMessage message, rest)
  else if tag = 103 then (RfqExecutionReportMessage.decode bytes).map fun (message, rest) => (.rfqExecutionReportMessage message, rest)
  else if tag = 106 then (BusinessRejectMessage.decode bytes).map fun (message, rest) => (.businessRejectMessage message, rest)
  else none

@[simp] theorem decode_encode (message : Payload) (rest : List UInt8) :
    decode (tag message) (encode message ++ rest) = some (message, rest) := by
  cases message <;> simp [decode, encode, tag]

end Payload

/-- Message -/
structure Message where
  startOfMessage : BitVec 8
  payload : Payload
  deriving DecidableEq, Repr

namespace Message

def encodeBody (message : Message) : List UInt8 :=
  encodeUInt 1 (Payload.tag message.payload)
    ++ (Payload.encode message.payload)

def decodeBody (startOfMessage : BitVec 8) (bytes : List UInt8) : Option (Message × List UInt8) := do
  let (messageType, bytes) ← decodeUInt 1 bytes
  let (payload, bytes) ← Payload.decode messageType bytes
  pure ({ startOfMessage, payload }, bytes)

theorem decodeBody_encodeBody (message : Message) (rest : List UInt8) :
    decodeBody message.startOfMessage (encodeBody message ++ rest) = some (message, rest) := by
  unfold decodeBody encodeBody
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [Payload.decode_encode, some_bind]
  rfl

/-- Every body fits the length prefix -/
theorem encodeBody_length_lt (message : Message) : (encodeBody message).length + 0 < 256 ^ 2 := by
  unfold encodeBody
  cases message.payload with
  | logonMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, LogonMessage.encode_length]
    omega
  | logonReplyMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, LogonReplyMessage.encode_length]
    omega
  | logoutMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, LogoutMessage.encode_length]
    omega
  | heartbeatMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, HeartbeatMessage.encode_length]
    omega
  | rejectMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, RejectMessage.encode_length]
    omega
  | systemStatusMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, SystemStatusMessage.encode_length]
    omega
  | newOrderMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, NewOrderMessage.encode_length]
    omega
  | newQuoteMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, NewQuoteMessage.encode_length]
    omega
  | orderCancelReplaceRequestMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, OrderCancelReplaceRequestMessage.encode_length]
    omega
  | orderCancelRequestMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, OrderCancelRequestMessage.encode_length]
    omega
  | orderMassCancelRequestMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, OrderMassCancelRequestMessage.encode_length]
    omega
  | executionReportMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, ExecutionReportMessage.encode_length]
    omega
  | orderCancelRejectMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, OrderCancelRejectMessage.encode_length]
    omega
  | orderMassCancelReportMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, OrderMassCancelReportMessage.encode_length]
    omega
  | quoteRequestMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, QuoteRequestMessage.encode_length]
    omega
  | quoteStatusReportMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, QuoteStatusReportMessage.encode_length]
    omega
  | quoteRequestRejectMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, QuoteRequestRejectMessage.encode_length]
    omega
  | rfqQuoteMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, RfqQuoteMessage.encode_length]
    omega
  | quoteAckMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, QuoteAckMessage.encode_length]
    omega
  | quoteResponseMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, QuoteResponseMessage.encode_length]
    omega
  | rfqExecutionReportMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, RfqExecutionReportMessage.encode_length]
    omega
  | businessRejectMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, BusinessRejectMessage.encode_length]
    omega

/-- Size rule: Message Length counts the bytes after it, so it is written from the body and checked on decode; Start Of Message is read ahead of it -/
def encode (message : Message) : List UInt8 :=
  encodeUInt 1 message.startOfMessage
    ++ (encodeFramedLE 2 0 encodeBody message)

def decode (bytes : List UInt8) : Option (Message × List UInt8) := do
  let (startOfMessage, bytes) ← decodeUInt 1 bytes
  decodeFramedLE 2 0 (decodeBody startOfMessage) bytes

@[simp] theorem decode_encode (message : Message) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  exact decodeFramedLE_encodeFramedLE 2 0 encodeBody (decodeBody message.startOfMessage) message (decodeBody_encodeBody message) (encodeBody_length_lt message) rest

theorem encode_length_pos (message : Message) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUInt_length, List.length_append, encodeFramedLE_length]
  omega

end Message

/-- Packet -/
structure Packet where
  message : List Message
  deriving DecidableEq, Repr

namespace Packet

def encode (message : Packet) : List UInt8 :=
  encodeMany Message.encode message.message

def decode (bytes : List UInt8) : Option Packet := do
  let message ← decodeAll Message.decode bytes.length bytes
  pure { message }

theorem decode_encode (message : Packet) : decode (encode message) = some message := by
  unfold decode encode
  rw [decodeAll_encodeMany Message.encode Message.decode Message.decode_encode Message.encode_length_pos message.message _ (encodeMany_length_ge Message.encode Message.encode_length_pos message.message), some_bind]
  rfl

end Packet

end Omi.LsegMillenniumNativetradinggatewayNtgiV212
