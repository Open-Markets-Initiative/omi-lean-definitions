import Omi.Wire

/-!
# Aquis Exchange Aquis Trading Protocol v4.0

Generated from the binary model, with the proofs the model's rules call for: every record
decodes back to what was encoded; a message dispatch selects the message its type names;
a count is written from the list it counts; a length prefix is written from the bytes it frames;
and a packet read to the end of its data decodes to the messages that were written.

Note: Flags is a bit field set, proven as its 1 byte integer rather than bit by bit.

Note: Table Select 1 is a bit field set, proven as its 1 byte integer rather than bit by bit.

Note: Table Select 2 is a bit field set, proven as its 1 byte integer rather than bit by bit.

Note: Table Select 3 is a bit field set, proven as its 1 byte integer rather than bit by bit.

Note: Extended Order Flags is a bit field set, proven as its 1 byte integer rather than bit by bit.

Note: Status is a bit field set, proven as its 1 byte integer rather than bit by bit.

Note: Order Add Response Flags is a bit field set, proven as its 1 byte integer rather than bit by bit.

Note: Trade Capture Flags is a bit field set, proven as its 1 byte integer rather than bit by bit.

Note: Trade Flags is a bit field set, proven as its 1 byte integer rather than bit by bit.

Note: Ioi Extended Flags is a bit field set, proven as its 1 byte integer rather than bit by bit.

Text fields are kept byte for byte, padding included, so what is decoded encodes back unchanged.
Prices with implied decimals are proven as the integers on the wire.
-/

namespace Omi.AquisAquisequitiesTradingprotocolAtpV40

/-- Login Message: 40 bytes -/
structure LoginMessage where
  protocolVersion : BitVec 16
  senderId : Alpha 16
  password : Alpha 16
  inactivityTimeout : BitVec 16
  atpSeqNo : BitVec 32
  deriving DecidableEq, Repr

namespace LoginMessage

def encode (message : LoginMessage) : List UInt8 :=
  encodeUIntLE 2 message.protocolVersion
    ++ (Alpha.encode message.senderId
    ++ (Alpha.encode message.password
    ++ (encodeUIntLE 2 message.inactivityTimeout
    ++ (encodeUIntLE 4 message.atpSeqNo))))

def decode (bytes : List UInt8) : Option (LoginMessage × List UInt8) := do
  let (protocolVersion, bytes) ← decodeUIntLE 2 bytes
  let (senderId, bytes) ← Alpha.decode 16 bytes
  let (password, bytes) ← Alpha.decode 16 bytes
  let (inactivityTimeout, bytes) ← decodeUIntLE 2 bytes
  let (atpSeqNo, bytes) ← decodeUIntLE 4 bytes
  pure ({ protocolVersion, senderId, password, inactivityTimeout, atpSeqNo }, bytes)

@[simp] theorem encode_length (message : LoginMessage) : (encode message).length = 40 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length]

theorem encode_length_pos (message : LoginMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : LoginMessage) (rest : List UInt8) :
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
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end LoginMessage

/-- Login Response Message: 5 bytes -/
structure LoginResponseMessage where
  resultCode : BitVec 8
  clientSeqNo : BitVec 32
  deriving DecidableEq, Repr

namespace LoginResponseMessage

def encode (message : LoginResponseMessage) : List UInt8 :=
  encodeUIntLE 1 message.resultCode
    ++ (encodeUIntLE 4 message.clientSeqNo)

def decode (bytes : List UInt8) : Option (LoginResponseMessage × List UInt8) := do
  let (resultCode, bytes) ← decodeUIntLE 1 bytes
  let (clientSeqNo, bytes) ← decodeUIntLE 4 bytes
  pure ({ resultCode, clientSeqNo }, bytes)

@[simp] theorem encode_length (message : LoginResponseMessage) : (encode message).length = 5 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length]

theorem encode_length_pos (message : LoginResponseMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : LoginResponseMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end LoginResponseMessage

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

/-- Logout Request Message: 0 bytes -/
structure LogoutRequestMessage where
  deriving DecidableEq, Repr

namespace LogoutRequestMessage

def encode (_ : LogoutRequestMessage) : List UInt8 :=
  []

def decode (bytes : List UInt8) : Option (LogoutRequestMessage × List UInt8) :=
  some (⟨⟩, bytes)

@[simp] theorem encode_length (message : LogoutRequestMessage) : (encode message).length = 0 := by
  simp [encode]

@[simp] theorem decode_encode (message : LogoutRequestMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  simp [decode, encode]

end LogoutRequestMessage

/-- Logout Message: 33 bytes -/
structure LogoutMessage where
  logoutReasonCode : BitVec 8
  reasonText : Alpha 32
  deriving DecidableEq, Repr

namespace LogoutMessage

def encode (message : LogoutMessage) : List UInt8 :=
  encodeUIntLE 1 message.logoutReasonCode
    ++ (Alpha.encode message.reasonText)

def decode (bytes : List UInt8) : Option (LogoutMessage × List UInt8) := do
  let (logoutReasonCode, bytes) ← decodeUIntLE 1 bytes
  let (reasonText, bytes) ← Alpha.decode 32 bytes
  pure ({ logoutReasonCode, reasonText }, bytes)

@[simp] theorem encode_length (message : LogoutMessage) : (encode message).length = 33 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length]

theorem encode_length_pos (message : LogoutMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : LogoutMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end LogoutMessage

/-- Order Add Message: 43 bytes -/
structure OrderAddMessage where
  securityIdShort : BitVec 16
  orderType : BitVec 8
  timeInForce : BitVec 8
  side : BitVec 8
  quantity : BitVec 32
  price : BitVec 64
  orderCapacity : BitVec 8
  account : BitVec 8
  userTag : BitVec 64
  flags : BitVec 8
  tableSelect1 : BitVec 8
  shortCode1 : BitVec 32
  tableSelect2 : BitVec 8
  shortCode2 : BitVec 32
  tableSelect3 : BitVec 8
  shortCode3 : BitVec 32
  deriving DecidableEq, Repr

namespace OrderAddMessage

def encode (message : OrderAddMessage) : List UInt8 :=
  encodeUIntLE 2 message.securityIdShort
    ++ (encodeUIntLE 1 message.orderType
    ++ (encodeUIntLE 1 message.timeInForce
    ++ (encodeUIntLE 1 message.side
    ++ (encodeUIntLE 4 message.quantity
    ++ (encodeUIntLE 8 message.price
    ++ (encodeUIntLE 1 message.orderCapacity
    ++ (encodeUIntLE 1 message.account
    ++ (encodeUIntLE 8 message.userTag
    ++ (encodeUIntLE 1 message.flags
    ++ (encodeUIntLE 1 message.tableSelect1
    ++ (encodeUIntLE 4 message.shortCode1
    ++ (encodeUIntLE 1 message.tableSelect2
    ++ (encodeUIntLE 4 message.shortCode2
    ++ (encodeUIntLE 1 message.tableSelect3
    ++ (encodeUIntLE 4 message.shortCode3)))))))))))))))

def decode (bytes : List UInt8) : Option (OrderAddMessage × List UInt8) := do
  let (securityIdShort, bytes) ← decodeUIntLE 2 bytes
  let (orderType, bytes) ← decodeUIntLE 1 bytes
  let (timeInForce, bytes) ← decodeUIntLE 1 bytes
  let (side, bytes) ← decodeUIntLE 1 bytes
  let (quantity, bytes) ← decodeUIntLE 4 bytes
  let (price, bytes) ← decodeUIntLE 8 bytes
  let (orderCapacity, bytes) ← decodeUIntLE 1 bytes
  let (account, bytes) ← decodeUIntLE 1 bytes
  let (userTag, bytes) ← decodeUIntLE 8 bytes
  let (flags, bytes) ← decodeUIntLE 1 bytes
  let (tableSelect1, bytes) ← decodeUIntLE 1 bytes
  let (shortCode1, bytes) ← decodeUIntLE 4 bytes
  let (tableSelect2, bytes) ← decodeUIntLE 1 bytes
  let (shortCode2, bytes) ← decodeUIntLE 4 bytes
  let (tableSelect3, bytes) ← decodeUIntLE 1 bytes
  let (shortCode3, bytes) ← decodeUIntLE 4 bytes
  pure ({ securityIdShort, orderType, timeInForce, side, quantity, price, orderCapacity, account, userTag, flags, tableSelect1, shortCode1, tableSelect2, shortCode2, tableSelect3, shortCode3 }, bytes)

@[simp] theorem encode_length (message : OrderAddMessage) : (encode message).length = 43 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length]

theorem encode_length_pos (message : OrderAddMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OrderAddMessage) (rest : List UInt8) :
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

end OrderAddMessage

/-- Order Add Extended Message: 78 bytes -/
structure OrderAddExtendedMessage where
  securityIdShort : BitVec 16
  orderType : BitVec 8
  timeInForce : BitVec 8
  side : BitVec 8
  quantity : BitVec 32
  price : BitVec 64
  orderCapacity : BitVec 8
  account : BitVec 8
  userTag : BitVec 64
  flags : BitVec 8
  tableSelect1 : BitVec 8
  shortCode1 : BitVec 32
  tableSelect2 : BitVec 8
  shortCode2 : BitVec 32
  tableSelect3 : BitVec 8
  shortCode3 : BitVec 32
  displayQuantity : BitVec 32
  minQty : BitVec 32
  extendedOrderFlags : BitVec 8
  reservedLong : BitVec 64
  designatedOrderId : BitVec 64
  reservedShort : BitVec 16
  pegDifference : BitVec 64
  deriving DecidableEq, Repr

namespace OrderAddExtendedMessage

def encode (message : OrderAddExtendedMessage) : List UInt8 :=
  encodeUIntLE 2 message.securityIdShort
    ++ (encodeUIntLE 1 message.orderType
    ++ (encodeUIntLE 1 message.timeInForce
    ++ (encodeUIntLE 1 message.side
    ++ (encodeUIntLE 4 message.quantity
    ++ (encodeUIntLE 8 message.price
    ++ (encodeUIntLE 1 message.orderCapacity
    ++ (encodeUIntLE 1 message.account
    ++ (encodeUIntLE 8 message.userTag
    ++ (encodeUIntLE 1 message.flags
    ++ (encodeUIntLE 1 message.tableSelect1
    ++ (encodeUIntLE 4 message.shortCode1
    ++ (encodeUIntLE 1 message.tableSelect2
    ++ (encodeUIntLE 4 message.shortCode2
    ++ (encodeUIntLE 1 message.tableSelect3
    ++ (encodeUIntLE 4 message.shortCode3
    ++ (encodeUIntLE 4 message.displayQuantity
    ++ (encodeUIntLE 4 message.minQty
    ++ (encodeUIntLE 1 message.extendedOrderFlags
    ++ (encodeUIntLE 8 message.reservedLong
    ++ (encodeUIntLE 8 message.designatedOrderId
    ++ (encodeUIntLE 2 message.reservedShort
    ++ (encodeUIntLE 8 message.pegDifference))))))))))))))))))))))

def decode (bytes : List UInt8) : Option (OrderAddExtendedMessage × List UInt8) := do
  let (securityIdShort, bytes) ← decodeUIntLE 2 bytes
  let (orderType, bytes) ← decodeUIntLE 1 bytes
  let (timeInForce, bytes) ← decodeUIntLE 1 bytes
  let (side, bytes) ← decodeUIntLE 1 bytes
  let (quantity, bytes) ← decodeUIntLE 4 bytes
  let (price, bytes) ← decodeUIntLE 8 bytes
  let (orderCapacity, bytes) ← decodeUIntLE 1 bytes
  let (account, bytes) ← decodeUIntLE 1 bytes
  let (userTag, bytes) ← decodeUIntLE 8 bytes
  let (flags, bytes) ← decodeUIntLE 1 bytes
  let (tableSelect1, bytes) ← decodeUIntLE 1 bytes
  let (shortCode1, bytes) ← decodeUIntLE 4 bytes
  let (tableSelect2, bytes) ← decodeUIntLE 1 bytes
  let (shortCode2, bytes) ← decodeUIntLE 4 bytes
  let (tableSelect3, bytes) ← decodeUIntLE 1 bytes
  let (shortCode3, bytes) ← decodeUIntLE 4 bytes
  let (displayQuantity, bytes) ← decodeUIntLE 4 bytes
  let (minQty, bytes) ← decodeUIntLE 4 bytes
  let (extendedOrderFlags, bytes) ← decodeUIntLE 1 bytes
  let (reservedLong, bytes) ← decodeUIntLE 8 bytes
  let (designatedOrderId, bytes) ← decodeUIntLE 8 bytes
  let (reservedShort, bytes) ← decodeUIntLE 2 bytes
  let (pegDifference, bytes) ← decodeUIntLE 8 bytes
  pure ({ securityIdShort, orderType, timeInForce, side, quantity, price, orderCapacity, account, userTag, flags, tableSelect1, shortCode1, tableSelect2, shortCode2, tableSelect3, shortCode3, displayQuantity, minQty, extendedOrderFlags, reservedLong, designatedOrderId, reservedShort, pegDifference }, bytes)

@[simp] theorem encode_length (message : OrderAddExtendedMessage) : (encode message).length = 78 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length]

theorem encode_length_pos (message : OrderAddExtendedMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OrderAddExtendedMessage) (rest : List UInt8) :
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
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end OrderAddExtendedMessage

/-- Order Cancel Message: 28 bytes -/
structure OrderCancelMessage where
  orderRef : BitVec 32
  userTag : BitVec 64
  flags : BitVec 8
  tableSelect1 : BitVec 8
  shortCode1 : BitVec 32
  tableSelect2 : BitVec 8
  shortCode2 : BitVec 32
  tableSelect3 : BitVec 8
  shortCode3 : BitVec 32
  deriving DecidableEq, Repr

namespace OrderCancelMessage

def encode (message : OrderCancelMessage) : List UInt8 :=
  encodeUIntLE 4 message.orderRef
    ++ (encodeUIntLE 8 message.userTag
    ++ (encodeUIntLE 1 message.flags
    ++ (encodeUIntLE 1 message.tableSelect1
    ++ (encodeUIntLE 4 message.shortCode1
    ++ (encodeUIntLE 1 message.tableSelect2
    ++ (encodeUIntLE 4 message.shortCode2
    ++ (encodeUIntLE 1 message.tableSelect3
    ++ (encodeUIntLE 4 message.shortCode3))))))))

def decode (bytes : List UInt8) : Option (OrderCancelMessage × List UInt8) := do
  let (orderRef, bytes) ← decodeUIntLE 4 bytes
  let (userTag, bytes) ← decodeUIntLE 8 bytes
  let (flags, bytes) ← decodeUIntLE 1 bytes
  let (tableSelect1, bytes) ← decodeUIntLE 1 bytes
  let (shortCode1, bytes) ← decodeUIntLE 4 bytes
  let (tableSelect2, bytes) ← decodeUIntLE 1 bytes
  let (shortCode2, bytes) ← decodeUIntLE 4 bytes
  let (tableSelect3, bytes) ← decodeUIntLE 1 bytes
  let (shortCode3, bytes) ← decodeUIntLE 4 bytes
  pure ({ orderRef, userTag, flags, tableSelect1, shortCode1, tableSelect2, shortCode2, tableSelect3, shortCode3 }, bytes)

@[simp] theorem encode_length (message : OrderCancelMessage) : (encode message).length = 28 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length]

theorem encode_length_pos (message : OrderCancelMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OrderCancelMessage) (rest : List UInt8) :
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

end OrderCancelMessage

/-- Order Modify Message: 41 bytes -/
structure OrderModifyMessage where
  orderRef : BitVec 32
  price : BitVec 64
  quantity : BitVec 32
  userTag : BitVec 64
  flags : BitVec 8
  tableSelect1 : BitVec 8
  shortCode1 : BitVec 32
  tableSelect2 : BitVec 8
  shortCode2 : BitVec 32
  tableSelect3 : BitVec 8
  shortCode3 : BitVec 32
  orderCapacity : BitVec 8
  deriving DecidableEq, Repr

namespace OrderModifyMessage

def encode (message : OrderModifyMessage) : List UInt8 :=
  encodeUIntLE 4 message.orderRef
    ++ (encodeUIntLE 8 message.price
    ++ (encodeUIntLE 4 message.quantity
    ++ (encodeUIntLE 8 message.userTag
    ++ (encodeUIntLE 1 message.flags
    ++ (encodeUIntLE 1 message.tableSelect1
    ++ (encodeUIntLE 4 message.shortCode1
    ++ (encodeUIntLE 1 message.tableSelect2
    ++ (encodeUIntLE 4 message.shortCode2
    ++ (encodeUIntLE 1 message.tableSelect3
    ++ (encodeUIntLE 4 message.shortCode3
    ++ (encodeUIntLE 1 message.orderCapacity)))))))))))

def decode (bytes : List UInt8) : Option (OrderModifyMessage × List UInt8) := do
  let (orderRef, bytes) ← decodeUIntLE 4 bytes
  let (price, bytes) ← decodeUIntLE 8 bytes
  let (quantity, bytes) ← decodeUIntLE 4 bytes
  let (userTag, bytes) ← decodeUIntLE 8 bytes
  let (flags, bytes) ← decodeUIntLE 1 bytes
  let (tableSelect1, bytes) ← decodeUIntLE 1 bytes
  let (shortCode1, bytes) ← decodeUIntLE 4 bytes
  let (tableSelect2, bytes) ← decodeUIntLE 1 bytes
  let (shortCode2, bytes) ← decodeUIntLE 4 bytes
  let (tableSelect3, bytes) ← decodeUIntLE 1 bytes
  let (shortCode3, bytes) ← decodeUIntLE 4 bytes
  let (orderCapacity, bytes) ← decodeUIntLE 1 bytes
  pure ({ orderRef, price, quantity, userTag, flags, tableSelect1, shortCode1, tableSelect2, shortCode2, tableSelect3, shortCode3, orderCapacity }, bytes)

@[simp] theorem encode_length (message : OrderModifyMessage) : (encode message).length = 41 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length]

theorem encode_length_pos (message : OrderModifyMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OrderModifyMessage) (rest : List UInt8) :
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

end OrderModifyMessage

/-- Order Modify Extended Message: 57 bytes -/
structure OrderModifyExtendedMessage where
  orderRef : BitVec 32
  price : BitVec 64
  quantity : BitVec 32
  userTag : BitVec 64
  flags : BitVec 8
  tableSelect1 : BitVec 8
  shortCode1 : BitVec 32
  tableSelect2 : BitVec 8
  shortCode2 : BitVec 32
  tableSelect3 : BitVec 8
  shortCode3 : BitVec 32
  orderCapacity : BitVec 8
  displayQuantity : BitVec 32
  minQty : BitVec 32
  reservedLong : BitVec 64
  deriving DecidableEq, Repr

namespace OrderModifyExtendedMessage

def encode (message : OrderModifyExtendedMessage) : List UInt8 :=
  encodeUIntLE 4 message.orderRef
    ++ (encodeUIntLE 8 message.price
    ++ (encodeUIntLE 4 message.quantity
    ++ (encodeUIntLE 8 message.userTag
    ++ (encodeUIntLE 1 message.flags
    ++ (encodeUIntLE 1 message.tableSelect1
    ++ (encodeUIntLE 4 message.shortCode1
    ++ (encodeUIntLE 1 message.tableSelect2
    ++ (encodeUIntLE 4 message.shortCode2
    ++ (encodeUIntLE 1 message.tableSelect3
    ++ (encodeUIntLE 4 message.shortCode3
    ++ (encodeUIntLE 1 message.orderCapacity
    ++ (encodeUIntLE 4 message.displayQuantity
    ++ (encodeUIntLE 4 message.minQty
    ++ (encodeUIntLE 8 message.reservedLong))))))))))))))

def decode (bytes : List UInt8) : Option (OrderModifyExtendedMessage × List UInt8) := do
  let (orderRef, bytes) ← decodeUIntLE 4 bytes
  let (price, bytes) ← decodeUIntLE 8 bytes
  let (quantity, bytes) ← decodeUIntLE 4 bytes
  let (userTag, bytes) ← decodeUIntLE 8 bytes
  let (flags, bytes) ← decodeUIntLE 1 bytes
  let (tableSelect1, bytes) ← decodeUIntLE 1 bytes
  let (shortCode1, bytes) ← decodeUIntLE 4 bytes
  let (tableSelect2, bytes) ← decodeUIntLE 1 bytes
  let (shortCode2, bytes) ← decodeUIntLE 4 bytes
  let (tableSelect3, bytes) ← decodeUIntLE 1 bytes
  let (shortCode3, bytes) ← decodeUIntLE 4 bytes
  let (orderCapacity, bytes) ← decodeUIntLE 1 bytes
  let (displayQuantity, bytes) ← decodeUIntLE 4 bytes
  let (minQty, bytes) ← decodeUIntLE 4 bytes
  let (reservedLong, bytes) ← decodeUIntLE 8 bytes
  pure ({ orderRef, price, quantity, userTag, flags, tableSelect1, shortCode1, tableSelect2, shortCode2, tableSelect3, shortCode3, orderCapacity, displayQuantity, minQty, reservedLong }, bytes)

@[simp] theorem encode_length (message : OrderModifyExtendedMessage) : (encode message).length = 57 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length]

theorem encode_length_pos (message : OrderModifyExtendedMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OrderModifyExtendedMessage) (rest : List UInt8) :
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

end OrderModifyExtendedMessage

/-- Order Add Response Message: 30 bytes -/
structure OrderAddResponseMessage where
  orderRef : BitVec 32
  marketDataId : BitVec 32
  status : BitVec 8
  tradedQuantity : BitVec 32
  timestamp : BitVec 64
  userTag : BitVec 64
  orderAddResponseFlags : BitVec 8
  deriving DecidableEq, Repr

namespace OrderAddResponseMessage

def encode (message : OrderAddResponseMessage) : List UInt8 :=
  encodeUIntLE 4 message.orderRef
    ++ (encodeUIntLE 4 message.marketDataId
    ++ (encodeUIntLE 1 message.status
    ++ (encodeUIntLE 4 message.tradedQuantity
    ++ (encodeUIntLE 8 message.timestamp
    ++ (encodeUIntLE 8 message.userTag
    ++ (encodeUIntLE 1 message.orderAddResponseFlags))))))

def decode (bytes : List UInt8) : Option (OrderAddResponseMessage × List UInt8) := do
  let (orderRef, bytes) ← decodeUIntLE 4 bytes
  let (marketDataId, bytes) ← decodeUIntLE 4 bytes
  let (status, bytes) ← decodeUIntLE 1 bytes
  let (tradedQuantity, bytes) ← decodeUIntLE 4 bytes
  let (timestamp, bytes) ← decodeUIntLE 8 bytes
  let (userTag, bytes) ← decodeUIntLE 8 bytes
  let (orderAddResponseFlags, bytes) ← decodeUIntLE 1 bytes
  pure ({ orderRef, marketDataId, status, tradedQuantity, timestamp, userTag, orderAddResponseFlags }, bytes)

@[simp] theorem encode_length (message : OrderAddResponseMessage) : (encode message).length = 30 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length]

theorem encode_length_pos (message : OrderAddResponseMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OrderAddResponseMessage) (rest : List UInt8) :
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
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end OrderAddResponseMessage

/-- Order Cancel Response Message: 25 bytes -/
structure OrderCancelResponseMessage where
  orderRef : BitVec 32
  requestRef : BitVec 32
  status : BitVec 8
  timestamp : BitVec 64
  userTag : BitVec 64
  deriving DecidableEq, Repr

namespace OrderCancelResponseMessage

def encode (message : OrderCancelResponseMessage) : List UInt8 :=
  encodeUIntLE 4 message.orderRef
    ++ (encodeUIntLE 4 message.requestRef
    ++ (encodeUIntLE 1 message.status
    ++ (encodeUIntLE 8 message.timestamp
    ++ (encodeUIntLE 8 message.userTag))))

def decode (bytes : List UInt8) : Option (OrderCancelResponseMessage × List UInt8) := do
  let (orderRef, bytes) ← decodeUIntLE 4 bytes
  let (requestRef, bytes) ← decodeUIntLE 4 bytes
  let (status, bytes) ← decodeUIntLE 1 bytes
  let (timestamp, bytes) ← decodeUIntLE 8 bytes
  let (userTag, bytes) ← decodeUIntLE 8 bytes
  pure ({ orderRef, requestRef, status, timestamp, userTag }, bytes)

@[simp] theorem encode_length (message : OrderCancelResponseMessage) : (encode message).length = 25 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length]

theorem encode_length_pos (message : OrderCancelResponseMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OrderCancelResponseMessage) (rest : List UInt8) :
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
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end OrderCancelResponseMessage

/-- Order Modify Response Message: 26 bytes -/
structure OrderModifyResponseMessage where
  orderRef : BitVec 32
  requestRef : BitVec 32
  status : BitVec 8
  timestamp : BitVec 64
  userTag : BitVec 64
  orderModifyResponseFlagsU81 : BitVec 8
  deriving DecidableEq, Repr

namespace OrderModifyResponseMessage

def encode (message : OrderModifyResponseMessage) : List UInt8 :=
  encodeUIntLE 4 message.orderRef
    ++ (encodeUIntLE 4 message.requestRef
    ++ (encodeUIntLE 1 message.status
    ++ (encodeUIntLE 8 message.timestamp
    ++ (encodeUIntLE 8 message.userTag
    ++ (encodeUIntLE 1 message.orderModifyResponseFlagsU81)))))

def decode (bytes : List UInt8) : Option (OrderModifyResponseMessage × List UInt8) := do
  let (orderRef, bytes) ← decodeUIntLE 4 bytes
  let (requestRef, bytes) ← decodeUIntLE 4 bytes
  let (status, bytes) ← decodeUIntLE 1 bytes
  let (timestamp, bytes) ← decodeUIntLE 8 bytes
  let (userTag, bytes) ← decodeUIntLE 8 bytes
  let (orderModifyResponseFlagsU81, bytes) ← decodeUIntLE 1 bytes
  pure ({ orderRef, requestRef, status, timestamp, userTag, orderModifyResponseFlagsU81 }, bytes)

@[simp] theorem encode_length (message : OrderModifyResponseMessage) : (encode message).length = 26 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length]

theorem encode_length_pos (message : OrderModifyResponseMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OrderModifyResponseMessage) (rest : List UInt8) :
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
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end OrderModifyResponseMessage

/-- Iceberg Order Refresh Message: 16 bytes -/
structure IcebergOrderRefreshMessage where
  orderRef : BitVec 32
  origAqxOrdId : BitVec 32
  newAqxOrdId : BitVec 32
  quantity : BitVec 32
  deriving DecidableEq, Repr

namespace IcebergOrderRefreshMessage

def encode (message : IcebergOrderRefreshMessage) : List UInt8 :=
  encodeUIntLE 4 message.orderRef
    ++ (encodeUIntLE 4 message.origAqxOrdId
    ++ (encodeUIntLE 4 message.newAqxOrdId
    ++ (encodeUIntLE 4 message.quantity)))

def decode (bytes : List UInt8) : Option (IcebergOrderRefreshMessage × List UInt8) := do
  let (orderRef, bytes) ← decodeUIntLE 4 bytes
  let (origAqxOrdId, bytes) ← decodeUIntLE 4 bytes
  let (newAqxOrdId, bytes) ← decodeUIntLE 4 bytes
  let (quantity, bytes) ← decodeUIntLE 4 bytes
  pure ({ orderRef, origAqxOrdId, newAqxOrdId, quantity }, bytes)

@[simp] theorem encode_length (message : IcebergOrderRefreshMessage) : (encode message).length = 16 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length]

theorem encode_length_pos (message : IcebergOrderRefreshMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : IcebergOrderRefreshMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end IcebergOrderRefreshMessage

/-- Trade Capture Message: 27 bytes -/
structure TradeCaptureMessage where
  quantity : BitVec 32
  price : BitVec 64
  securityIdLong : BitVec 32
  tradeCaptureType : BitVec 8
  tradeCaptureFlags : BitVec 8
  account : BitVec 8
  userTag : BitVec 64
  deriving DecidableEq, Repr

namespace TradeCaptureMessage

def encode (message : TradeCaptureMessage) : List UInt8 :=
  encodeUIntLE 4 message.quantity
    ++ (encodeUIntLE 8 message.price
    ++ (encodeUIntLE 4 message.securityIdLong
    ++ (encodeUIntLE 1 message.tradeCaptureType
    ++ (encodeUIntLE 1 message.tradeCaptureFlags
    ++ (encodeUIntLE 1 message.account
    ++ (encodeUIntLE 8 message.userTag))))))

def decode (bytes : List UInt8) : Option (TradeCaptureMessage × List UInt8) := do
  let (quantity, bytes) ← decodeUIntLE 4 bytes
  let (price, bytes) ← decodeUIntLE 8 bytes
  let (securityIdLong, bytes) ← decodeUIntLE 4 bytes
  let (tradeCaptureType, bytes) ← decodeUIntLE 1 bytes
  let (tradeCaptureFlags, bytes) ← decodeUIntLE 1 bytes
  let (account, bytes) ← decodeUIntLE 1 bytes
  let (userTag, bytes) ← decodeUIntLE 8 bytes
  pure ({ quantity, price, securityIdLong, tradeCaptureType, tradeCaptureFlags, account, userTag }, bytes)

@[simp] theorem encode_length (message : TradeCaptureMessage) : (encode message).length = 27 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length]

theorem encode_length_pos (message : TradeCaptureMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : TradeCaptureMessage) (rest : List UInt8) :
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
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end TradeCaptureMessage

/-- Trade Capture Response Message: 17 bytes -/
structure TradeCaptureResponseMessage where
  status : BitVec 8
  tradeRef : BitVec 32
  requestRef : BitVec 32
  userTag : BitVec 64
  deriving DecidableEq, Repr

namespace TradeCaptureResponseMessage

def encode (message : TradeCaptureResponseMessage) : List UInt8 :=
  encodeUIntLE 1 message.status
    ++ (encodeUIntLE 4 message.tradeRef
    ++ (encodeUIntLE 4 message.requestRef
    ++ (encodeUIntLE 8 message.userTag)))

def decode (bytes : List UInt8) : Option (TradeCaptureResponseMessage × List UInt8) := do
  let (status, bytes) ← decodeUIntLE 1 bytes
  let (tradeRef, bytes) ← decodeUIntLE 4 bytes
  let (requestRef, bytes) ← decodeUIntLE 4 bytes
  let (userTag, bytes) ← decodeUIntLE 8 bytes
  pure ({ status, tradeRef, requestRef, userTag }, bytes)

@[simp] theorem encode_length (message : TradeCaptureResponseMessage) : (encode message).length = 17 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length]

theorem encode_length_pos (message : TradeCaptureResponseMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : TradeCaptureResponseMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end TradeCaptureResponseMessage

/-- Trade Message: 42 bytes -/
structure TradeMessage where
  orderRef : BitVec 32
  quantity : BitVec 32
  price : BitVec 64
  side : BitVec 8
  tradeRef : BitVec 32
  ccpCode : BitVec 8
  liqIndicator : BitVec 8
  securityIdShort : BitVec 16
  timestamp : BitVec 64
  userTag : BitVec 64
  tradeFlags : BitVec 8
  deriving DecidableEq, Repr

namespace TradeMessage

def encode (message : TradeMessage) : List UInt8 :=
  encodeUIntLE 4 message.orderRef
    ++ (encodeUIntLE 4 message.quantity
    ++ (encodeUIntLE 8 message.price
    ++ (encodeUIntLE 1 message.side
    ++ (encodeUIntLE 4 message.tradeRef
    ++ (encodeUIntLE 1 message.ccpCode
    ++ (encodeUIntLE 1 message.liqIndicator
    ++ (encodeUIntLE 2 message.securityIdShort
    ++ (encodeUIntLE 8 message.timestamp
    ++ (encodeUIntLE 8 message.userTag
    ++ (encodeUIntLE 1 message.tradeFlags))))))))))

def decode (bytes : List UInt8) : Option (TradeMessage × List UInt8) := do
  let (orderRef, bytes) ← decodeUIntLE 4 bytes
  let (quantity, bytes) ← decodeUIntLE 4 bytes
  let (price, bytes) ← decodeUIntLE 8 bytes
  let (side, bytes) ← decodeUIntLE 1 bytes
  let (tradeRef, bytes) ← decodeUIntLE 4 bytes
  let (ccpCode, bytes) ← decodeUIntLE 1 bytes
  let (liqIndicator, bytes) ← decodeUIntLE 1 bytes
  let (securityIdShort, bytes) ← decodeUIntLE 2 bytes
  let (timestamp, bytes) ← decodeUIntLE 8 bytes
  let (userTag, bytes) ← decodeUIntLE 8 bytes
  let (tradeFlags, bytes) ← decodeUIntLE 1 bytes
  pure ({ orderRef, quantity, price, side, tradeRef, ccpCode, liqIndicator, securityIdShort, timestamp, userTag, tradeFlags }, bytes)

@[simp] theorem encode_length (message : TradeMessage) : (encode message).length = 42 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length]

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

end TradeMessage

/-- Trade Bust Message: 29 bytes -/
structure TradeBustMessage where
  orderRef : BitVec 32
  quantity : BitVec 32
  price : BitVec 64
  side : BitVec 8
  tradeRef : BitVec 32
  timestamp : BitVec 64
  deriving DecidableEq, Repr

namespace TradeBustMessage

def encode (message : TradeBustMessage) : List UInt8 :=
  encodeUIntLE 4 message.orderRef
    ++ (encodeUIntLE 4 message.quantity
    ++ (encodeUIntLE 8 message.price
    ++ (encodeUIntLE 1 message.side
    ++ (encodeUIntLE 4 message.tradeRef
    ++ (encodeUIntLE 8 message.timestamp)))))

def decode (bytes : List UInt8) : Option (TradeBustMessage × List UInt8) := do
  let (orderRef, bytes) ← decodeUIntLE 4 bytes
  let (quantity, bytes) ← decodeUIntLE 4 bytes
  let (price, bytes) ← decodeUIntLE 8 bytes
  let (side, bytes) ← decodeUIntLE 1 bytes
  let (tradeRef, bytes) ← decodeUIntLE 4 bytes
  let (timestamp, bytes) ← decodeUIntLE 8 bytes
  pure ({ orderRef, quantity, price, side, tradeRef, timestamp }, bytes)

@[simp] theorem encode_length (message : TradeBustMessage) : (encode message).length = 29 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length]

theorem encode_length_pos (message : TradeBustMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : TradeBustMessage) (rest : List UInt8) :
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
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end TradeBustMessage

/-- Ioi Add Message: 99 bytes -/
structure IoiAddMessage where
  securityIdShort : BitVec 16
  ioiOrderType : BitVec 8
  timeInForce : BitVec 8
  side : BitVec 8
  quantity : BitVec 32
  price : BitVec 64
  orderCapacity : BitVec 8
  account : BitVec 8
  userTag : BitVec 64
  flags : BitVec 8
  tableSelect1 : BitVec 8
  shortCode1 : BitVec 32
  tableSelect2 : BitVec 8
  shortCode2 : BitVec 32
  tableSelect3 : BitVec 8
  shortCode3 : BitVec 32
  minQty : BitVec 32
  ioiExtendedFlags : BitVec 8
  optimXUniverse : BitVec 8
  blotterBlacklist : Alpha 50
  deriving DecidableEq, Repr

namespace IoiAddMessage

def encode (message : IoiAddMessage) : List UInt8 :=
  encodeUIntLE 2 message.securityIdShort
    ++ (encodeUIntLE 1 message.ioiOrderType
    ++ (encodeUIntLE 1 message.timeInForce
    ++ (encodeUIntLE 1 message.side
    ++ (encodeUIntLE 4 message.quantity
    ++ (encodeUIntLE 8 message.price
    ++ (encodeUIntLE 1 message.orderCapacity
    ++ (encodeUIntLE 1 message.account
    ++ (encodeUIntLE 8 message.userTag
    ++ (encodeUIntLE 1 message.flags
    ++ (encodeUIntLE 1 message.tableSelect1
    ++ (encodeUIntLE 4 message.shortCode1
    ++ (encodeUIntLE 1 message.tableSelect2
    ++ (encodeUIntLE 4 message.shortCode2
    ++ (encodeUIntLE 1 message.tableSelect3
    ++ (encodeUIntLE 4 message.shortCode3
    ++ (encodeUIntLE 4 message.minQty
    ++ (encodeUIntLE 1 message.ioiExtendedFlags
    ++ (encodeUIntLE 1 message.optimXUniverse
    ++ (Alpha.encode message.blotterBlacklist)))))))))))))))))))

def decode (bytes : List UInt8) : Option (IoiAddMessage × List UInt8) := do
  let (securityIdShort, bytes) ← decodeUIntLE 2 bytes
  let (ioiOrderType, bytes) ← decodeUIntLE 1 bytes
  let (timeInForce, bytes) ← decodeUIntLE 1 bytes
  let (side, bytes) ← decodeUIntLE 1 bytes
  let (quantity, bytes) ← decodeUIntLE 4 bytes
  let (price, bytes) ← decodeUIntLE 8 bytes
  let (orderCapacity, bytes) ← decodeUIntLE 1 bytes
  let (account, bytes) ← decodeUIntLE 1 bytes
  let (userTag, bytes) ← decodeUIntLE 8 bytes
  let (flags, bytes) ← decodeUIntLE 1 bytes
  let (tableSelect1, bytes) ← decodeUIntLE 1 bytes
  let (shortCode1, bytes) ← decodeUIntLE 4 bytes
  let (tableSelect2, bytes) ← decodeUIntLE 1 bytes
  let (shortCode2, bytes) ← decodeUIntLE 4 bytes
  let (tableSelect3, bytes) ← decodeUIntLE 1 bytes
  let (shortCode3, bytes) ← decodeUIntLE 4 bytes
  let (minQty, bytes) ← decodeUIntLE 4 bytes
  let (ioiExtendedFlags, bytes) ← decodeUIntLE 1 bytes
  let (optimXUniverse, bytes) ← decodeUIntLE 1 bytes
  let (blotterBlacklist, bytes) ← Alpha.decode 50 bytes
  pure ({ securityIdShort, ioiOrderType, timeInForce, side, quantity, price, orderCapacity, account, userTag, flags, tableSelect1, shortCode1, tableSelect2, shortCode2, tableSelect3, shortCode3, minQty, ioiExtendedFlags, optimXUniverse, blotterBlacklist }, bytes)

@[simp] theorem encode_length (message : IoiAddMessage) : (encode message).length = 99 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length]

theorem encode_length_pos (message : IoiAddMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : IoiAddMessage) (rest : List UInt8) :
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

end IoiAddMessage

/-- Ioi Invite Message: 36 bytes -/
structure IoiInviteMessage where
  orderRef : BitVec 32
  price : BitVec 64
  quantity : BitVec 32
  minQty : BitVec 32
  timestamp : BitVec 64
  userTag : BitVec 64
  deriving DecidableEq, Repr

namespace IoiInviteMessage

def encode (message : IoiInviteMessage) : List UInt8 :=
  encodeUIntLE 4 message.orderRef
    ++ (encodeUIntLE 8 message.price
    ++ (encodeUIntLE 4 message.quantity
    ++ (encodeUIntLE 4 message.minQty
    ++ (encodeUIntLE 8 message.timestamp
    ++ (encodeUIntLE 8 message.userTag)))))

def decode (bytes : List UInt8) : Option (IoiInviteMessage × List UInt8) := do
  let (orderRef, bytes) ← decodeUIntLE 4 bytes
  let (price, bytes) ← decodeUIntLE 8 bytes
  let (quantity, bytes) ← decodeUIntLE 4 bytes
  let (minQty, bytes) ← decodeUIntLE 4 bytes
  let (timestamp, bytes) ← decodeUIntLE 8 bytes
  let (userTag, bytes) ← decodeUIntLE 8 bytes
  pure ({ orderRef, price, quantity, minQty, timestamp, userTag }, bytes)

@[simp] theorem encode_length (message : IoiInviteMessage) : (encode message).length = 36 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length]

theorem encode_length_pos (message : IoiInviteMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : IoiInviteMessage) (rest : List UInt8) :
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
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end IoiInviteMessage

/-- Ioi Firmup Message: 28 bytes -/
structure IoiFirmupMessage where
  orderRef : BitVec 32
  price : BitVec 64
  quantity : BitVec 32
  minQty : BitVec 32
  userTag : BitVec 64
  deriving DecidableEq, Repr

namespace IoiFirmupMessage

def encode (message : IoiFirmupMessage) : List UInt8 :=
  encodeUIntLE 4 message.orderRef
    ++ (encodeUIntLE 8 message.price
    ++ (encodeUIntLE 4 message.quantity
    ++ (encodeUIntLE 4 message.minQty
    ++ (encodeUIntLE 8 message.userTag))))

def decode (bytes : List UInt8) : Option (IoiFirmupMessage × List UInt8) := do
  let (orderRef, bytes) ← decodeUIntLE 4 bytes
  let (price, bytes) ← decodeUIntLE 8 bytes
  let (quantity, bytes) ← decodeUIntLE 4 bytes
  let (minQty, bytes) ← decodeUIntLE 4 bytes
  let (userTag, bytes) ← decodeUIntLE 8 bytes
  pure ({ orderRef, price, quantity, minQty, userTag }, bytes)

@[simp] theorem encode_length (message : IoiFirmupMessage) : (encode message).length = 28 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length]

theorem encode_length_pos (message : IoiFirmupMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : IoiFirmupMessage) (rest : List UInt8) :
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
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end IoiFirmupMessage

/-- Any Payload, selected by Msg Type -/
inductive Payload where
  | loginMessage (message : LoginMessage) -- 1
  | loginResponseMessage (message : LoginResponseMessage) -- 2
  | heartbeat (message : Heartbeat) -- 0
  | logoutRequestMessage (message : LogoutRequestMessage) -- 3
  | logoutMessage (message : LogoutMessage) -- 4
  | orderAddMessage (message : OrderAddMessage) -- 5
  | orderAddExtendedMessage (message : OrderAddExtendedMessage) -- 21
  | orderCancelMessage (message : OrderCancelMessage) -- 7
  | orderModifyMessage (message : OrderModifyMessage) -- 9
  | orderModifyExtendedMessage (message : OrderModifyExtendedMessage) -- 22
  | orderAddResponseMessage (message : OrderAddResponseMessage) -- 6
  | orderCancelResponseMessage (message : OrderCancelResponseMessage) -- 8
  | orderModifyResponseMessage (message : OrderModifyResponseMessage) -- 10
  | icebergOrderRefreshMessage (message : IcebergOrderRefreshMessage) -- 23
  | tradeCaptureMessage (message : TradeCaptureMessage) -- 17
  | tradeCaptureResponseMessage (message : TradeCaptureResponseMessage) -- 18
  | tradeMessage (message : TradeMessage) -- 11
  | tradeBustMessage (message : TradeBustMessage) -- 12
  | ioiAddMessage (message : IoiAddMessage) -- 27
  | ioiInviteMessage (message : IoiInviteMessage) -- 28
  | ioiFirmupMessage (message : IoiFirmupMessage) -- 29
  deriving DecidableEq, Repr

namespace Payload

/-- The Msg Type each message is sent under -/
def tag : Payload → BitVec 8
  | .loginMessage _ => 1
  | .loginResponseMessage _ => 2
  | .heartbeat _ => 0
  | .logoutRequestMessage _ => 3
  | .logoutMessage _ => 4
  | .orderAddMessage _ => 5
  | .orderAddExtendedMessage _ => 21
  | .orderCancelMessage _ => 7
  | .orderModifyMessage _ => 9
  | .orderModifyExtendedMessage _ => 22
  | .orderAddResponseMessage _ => 6
  | .orderCancelResponseMessage _ => 8
  | .orderModifyResponseMessage _ => 10
  | .icebergOrderRefreshMessage _ => 23
  | .tradeCaptureMessage _ => 17
  | .tradeCaptureResponseMessage _ => 18
  | .tradeMessage _ => 11
  | .tradeBustMessage _ => 12
  | .ioiAddMessage _ => 27
  | .ioiInviteMessage _ => 28
  | .ioiFirmupMessage _ => 29

def encode : Payload → List UInt8
  | .loginMessage message => LoginMessage.encode message
  | .loginResponseMessage message => LoginResponseMessage.encode message
  | .heartbeat message => Heartbeat.encode message
  | .logoutRequestMessage message => LogoutRequestMessage.encode message
  | .logoutMessage message => LogoutMessage.encode message
  | .orderAddMessage message => OrderAddMessage.encode message
  | .orderAddExtendedMessage message => OrderAddExtendedMessage.encode message
  | .orderCancelMessage message => OrderCancelMessage.encode message
  | .orderModifyMessage message => OrderModifyMessage.encode message
  | .orderModifyExtendedMessage message => OrderModifyExtendedMessage.encode message
  | .orderAddResponseMessage message => OrderAddResponseMessage.encode message
  | .orderCancelResponseMessage message => OrderCancelResponseMessage.encode message
  | .orderModifyResponseMessage message => OrderModifyResponseMessage.encode message
  | .icebergOrderRefreshMessage message => IcebergOrderRefreshMessage.encode message
  | .tradeCaptureMessage message => TradeCaptureMessage.encode message
  | .tradeCaptureResponseMessage message => TradeCaptureResponseMessage.encode message
  | .tradeMessage message => TradeMessage.encode message
  | .tradeBustMessage message => TradeBustMessage.encode message
  | .ioiAddMessage message => IoiAddMessage.encode message
  | .ioiInviteMessage message => IoiInviteMessage.encode message
  | .ioiFirmupMessage message => IoiFirmupMessage.encode message

def decode (tag : BitVec 8) (bytes : List UInt8) : Option (Payload × List UInt8) :=
  if tag = 1 then (LoginMessage.decode bytes).map fun (message, rest) => (.loginMessage message, rest)
  else if tag = 2 then (LoginResponseMessage.decode bytes).map fun (message, rest) => (.loginResponseMessage message, rest)
  else if tag = 0 then (Heartbeat.decode bytes).map fun (message, rest) => (.heartbeat message, rest)
  else if tag = 3 then (LogoutRequestMessage.decode bytes).map fun (message, rest) => (.logoutRequestMessage message, rest)
  else if tag = 4 then (LogoutMessage.decode bytes).map fun (message, rest) => (.logoutMessage message, rest)
  else if tag = 5 then (OrderAddMessage.decode bytes).map fun (message, rest) => (.orderAddMessage message, rest)
  else if tag = 21 then (OrderAddExtendedMessage.decode bytes).map fun (message, rest) => (.orderAddExtendedMessage message, rest)
  else if tag = 7 then (OrderCancelMessage.decode bytes).map fun (message, rest) => (.orderCancelMessage message, rest)
  else if tag = 9 then (OrderModifyMessage.decode bytes).map fun (message, rest) => (.orderModifyMessage message, rest)
  else if tag = 22 then (OrderModifyExtendedMessage.decode bytes).map fun (message, rest) => (.orderModifyExtendedMessage message, rest)
  else if tag = 6 then (OrderAddResponseMessage.decode bytes).map fun (message, rest) => (.orderAddResponseMessage message, rest)
  else if tag = 8 then (OrderCancelResponseMessage.decode bytes).map fun (message, rest) => (.orderCancelResponseMessage message, rest)
  else if tag = 10 then (OrderModifyResponseMessage.decode bytes).map fun (message, rest) => (.orderModifyResponseMessage message, rest)
  else if tag = 23 then (IcebergOrderRefreshMessage.decode bytes).map fun (message, rest) => (.icebergOrderRefreshMessage message, rest)
  else if tag = 17 then (TradeCaptureMessage.decode bytes).map fun (message, rest) => (.tradeCaptureMessage message, rest)
  else if tag = 18 then (TradeCaptureResponseMessage.decode bytes).map fun (message, rest) => (.tradeCaptureResponseMessage message, rest)
  else if tag = 11 then (TradeMessage.decode bytes).map fun (message, rest) => (.tradeMessage message, rest)
  else if tag = 12 then (TradeBustMessage.decode bytes).map fun (message, rest) => (.tradeBustMessage message, rest)
  else if tag = 27 then (IoiAddMessage.decode bytes).map fun (message, rest) => (.ioiAddMessage message, rest)
  else if tag = 28 then (IoiInviteMessage.decode bytes).map fun (message, rest) => (.ioiInviteMessage message, rest)
  else if tag = 29 then (IoiFirmupMessage.decode bytes).map fun (message, rest) => (.ioiFirmupMessage message, rest)
  else none

@[simp] theorem decode_encode (message : Payload) (rest : List UInt8) :
    decode (tag message) (encode message ++ rest) = some (message, rest) := by
  cases message <;> simp [decode, encode, tag]

end Payload

/-- Message -/
structure Message where
  msgSeqNo : BitVec 32
  payload : Payload
  deriving DecidableEq, Repr

namespace Message

def encodeBody (message : Message) : List UInt8 :=
  encodeUInt 1 (Payload.tag message.payload)
    ++ (encodeUIntLE 4 message.msgSeqNo
    ++ (Payload.encode message.payload))

def decodeBody (bytes : List UInt8) : Option (Message × List UInt8) := do
  let (msgType, bytes) ← decodeUInt 1 bytes
  let (msgSeqNo, bytes) ← decodeUIntLE 4 bytes
  let (payload, bytes) ← Payload.decode msgType bytes
  pure ({ msgSeqNo, payload }, bytes)

theorem decodeBody_encodeBody (message : Message) (rest : List UInt8) :
    decodeBody (encodeBody message ++ rest) = some (message, rest) := by
  unfold decodeBody encodeBody
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [Payload.decode_encode, some_bind]
  rfl

/-- Every body fits the length prefix -/
theorem encodeBody_length_lt (message : Message) : (encodeBody message).length + 2 < 256 ^ 2 := by
  unfold encodeBody
  cases message.payload with
  | loginMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, encodeUIntLE_length, LoginMessage.encode_length]
    omega
  | loginResponseMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, encodeUIntLE_length, LoginResponseMessage.encode_length]
    omega
  | heartbeat inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, encodeUIntLE_length, Heartbeat.encode_length]
    omega
  | logoutRequestMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, encodeUIntLE_length, LogoutRequestMessage.encode_length]
    omega
  | logoutMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, encodeUIntLE_length, LogoutMessage.encode_length]
    omega
  | orderAddMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, encodeUIntLE_length, OrderAddMessage.encode_length]
    omega
  | orderAddExtendedMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, encodeUIntLE_length, OrderAddExtendedMessage.encode_length]
    omega
  | orderCancelMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, encodeUIntLE_length, OrderCancelMessage.encode_length]
    omega
  | orderModifyMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, encodeUIntLE_length, OrderModifyMessage.encode_length]
    omega
  | orderModifyExtendedMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, encodeUIntLE_length, OrderModifyExtendedMessage.encode_length]
    omega
  | orderAddResponseMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, encodeUIntLE_length, OrderAddResponseMessage.encode_length]
    omega
  | orderCancelResponseMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, encodeUIntLE_length, OrderCancelResponseMessage.encode_length]
    omega
  | orderModifyResponseMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, encodeUIntLE_length, OrderModifyResponseMessage.encode_length]
    omega
  | icebergOrderRefreshMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, encodeUIntLE_length, IcebergOrderRefreshMessage.encode_length]
    omega
  | tradeCaptureMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, encodeUIntLE_length, TradeCaptureMessage.encode_length]
    omega
  | tradeCaptureResponseMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, encodeUIntLE_length, TradeCaptureResponseMessage.encode_length]
    omega
  | tradeMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, encodeUIntLE_length, TradeMessage.encode_length]
    omega
  | tradeBustMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, encodeUIntLE_length, TradeBustMessage.encode_length]
    omega
  | ioiAddMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, encodeUIntLE_length, IoiAddMessage.encode_length]
    omega
  | ioiInviteMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, encodeUIntLE_length, IoiInviteMessage.encode_length]
    omega
  | ioiFirmupMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, encodeUIntLE_length, IoiFirmupMessage.encode_length]
    omega

/-- Size rule: Msg Length counts the bytes after it plus 2, so it is written from the body and checked on decode -/
def encode : Message → List UInt8 :=
  encodeFramedLE 2 2 encodeBody

def decode : List UInt8 → Option (Message × List UInt8) :=
  decodeFramedLE 2 2 decodeBody

@[simp] theorem decode_encode (message : Message) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) :=
  decodeFramedLE_encodeFramedLE 2 2 encodeBody decodeBody message (decodeBody_encodeBody message) (encodeBody_length_lt message) rest

theorem encode_length_pos (message : Message) : (encode message).length > 0 := by
  unfold encode
  rw [encodeFramedLE_length]
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

end Omi.AquisAquisequitiesTradingprotocolAtpV40
