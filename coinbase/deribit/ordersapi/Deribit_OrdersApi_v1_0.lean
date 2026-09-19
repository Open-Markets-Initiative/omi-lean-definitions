import Omi.Wire

/-!
# Coinbase Orders Api v1.0

Generated from the binary model, with the proofs the model's rules call for: every record
decodes back to what was encoded; a message dispatch selects the message its type names;
a count is written from the list it counts; a length prefix is written from the bytes it frames;
and a packet read to the end of its data decodes to the messages that were written.

Note: Session Flags is a bit field set, proven as its 1 byte integer rather than bit by bit.

Note: Flags Order Flags is a bit field set, proven as its 2 byte integer rather than bit by bit.

Note: Flags Replace Order Flags is a bit field set, proven as its 2 byte integer rather than bit by bit.

Note: Flags Mass Quote Flags is a bit field set, proven as its 1 byte integer rather than bit by bit.

Note: Bid Flags is a bit field set, proven as its 2 byte integer rather than bit by bit.

Note: Ask Flags is a bit field set, proven as its 2 byte integer rather than bit by bit.

Note: Flags Fill Flags is a bit field set, proven as its 1 byte integer rather than bit by bit.

Note: Flags Multi Part Event Flags is a bit field set, proven as its 1 byte integer rather than bit by bit.

Note: Flags Cancel Flags is a bit field set, proven as its 1 byte integer rather than bit by bit.

Note: Sbe Message's body has no bound its 2 byte Message Length must fit, so every message carries the proof its own encoding fits: the record is its body with that proof, checked as the frame is read.

Text fields are kept byte for byte, padding included, so what is decoded encodes back unchanged.
Prices with implied decimals are proven as the integers on the wire.
-/

namespace Omi.CoinbaseDeribitOrdersapiSbeV10

/-- Logon Message: 65 bytes -/
structure LogonMessage where
  clientId : Alpha 16
  secret : Alpha 48
  resetSeqNum : BitVec 8
  deriving DecidableEq, Repr

namespace LogonMessage

def encode (message : LogonMessage) : List UInt8 :=
  Alpha.encode message.clientId
    ++ (Alpha.encode message.secret
    ++ (encodeUInt 1 message.resetSeqNum))

def decode (bytes : List UInt8) : Option (LogonMessage × List UInt8) := do
  let (clientId, bytes) ← Alpha.decode 16 bytes
  let (secret, bytes) ← Alpha.decode 48 bytes
  let (resetSeqNum, bytes) ← decodeUInt 1 bytes
  pure ({ clientId, secret, resetSeqNum }, bytes)

@[simp] theorem encode_length (message : LogonMessage) : (encode message).length = 65 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length]

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
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end LogonMessage

/-- Logon Conf Message: 4 bytes -/
structure LogonConfMessage where
  heartbeatIntervalSeconds : BitVec 32
  deriving DecidableEq, Repr

namespace LogonConfMessage

def encode (message : LogonConfMessage) : List UInt8 :=
  encodeUIntLE 4 message.heartbeatIntervalSeconds

def decode (bytes : List UInt8) : Option (LogonConfMessage × List UInt8) := do
  let (heartbeatIntervalSeconds, bytes) ← decodeUIntLE 4 bytes
  pure ({ heartbeatIntervalSeconds }, bytes)

@[simp] theorem encode_length (message : LogonConfMessage) : (encode message).length = 4 := by
  unfold encode
  simp only [encodeUIntLE_length]

theorem encode_length_pos (message : LogonConfMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : LogonConfMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end LogonConfMessage

/-- Reason -/
structure Reason where
  reasonData : Bounded 1 UInt8
  deriving DecidableEq, Repr

namespace Reason

def encode (message : Reason) : List UInt8 :=
  encodeUInt 1 (BitVec.ofNat (8 * 1) message.reasonData.val.length)
    ++ (encodeMany Byte.encode message.reasonData.val)

def decode (bytes : List UInt8) : Option (Reason × List UInt8) := do
  let (reasonLength, bytes) ← decodeUInt 1 bytes
  let (reasonData_, bytes) ← decodeMany Byte.decode reasonLength.toNat bytes
  if fits_reasonData : reasonData_.length < 256 ^ 1 then
    pure ({ reasonData := ⟨reasonData_, fits_reasonData⟩ }, bytes)
  else none

theorem encode_length_pos (message : Reason) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUInt_length, List.length_append]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : Reason) : (encode message).length ≤ 256 := by
  have bound_reasonData := message.reasonData.length_lt
  unfold encode
  simp only [List.length_append, encodeUInt_length, encodeMany_length_const Byte.encode 1 Byte.encode_length]
  omega

@[simp] theorem decode_encode (message : Reason) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeMany_bounded 1 Byte.encode Byte.decode Byte.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.reasonData.length_lt]
  rfl

end Reason

/-- Logout Message -/
structure LogoutMessage where
  reason : Reason
  deriving DecidableEq, Repr

namespace LogoutMessage

def encode (message : LogoutMessage) : List UInt8 :=
  Reason.encode message.reason

def decode (bytes : List UInt8) : Option (LogoutMessage × List UInt8) := do
  let (reason, bytes) ← Reason.decode bytes
  pure ({ reason }, bytes)

theorem encode_length_pos (message : LogoutMessage) : (encode message).length > 0 := by
  have positive := Reason.encode_length_pos message.reason
  unfold encode
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : LogoutMessage) : (encode message).length ≤ 256 := by
  have bound_reason := Reason.encode_length_le message.reason
  unfold encode
  omega

@[simp] theorem decode_encode (message : LogoutMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [Reason.decode_encode, some_bind]
  rfl

end LogoutMessage

/-- Logged Out Message -/
structure LoggedOutMessage where
  reason : Reason
  deriving DecidableEq, Repr

namespace LoggedOutMessage

def encode (message : LoggedOutMessage) : List UInt8 :=
  Reason.encode message.reason

def decode (bytes : List UInt8) : Option (LoggedOutMessage × List UInt8) := do
  let (reason, bytes) ← Reason.decode bytes
  pure ({ reason }, bytes)

theorem encode_length_pos (message : LoggedOutMessage) : (encode message).length > 0 := by
  have positive := Reason.encode_length_pos message.reason
  unfold encode
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : LoggedOutMessage) : (encode message).length ≤ 256 := by
  have bound_reason := Reason.encode_length_le message.reason
  unfold encode
  omega

@[simp] theorem decode_encode (message : LoggedOutMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [Reason.decode_encode, some_bind]
  rfl

end LoggedOutMessage

/-- Heartbeat Message: 8 bytes -/
structure HeartbeatMessage where
  correlationId : BitVec 64
  deriving DecidableEq, Repr

namespace HeartbeatMessage

def encode (message : HeartbeatMessage) : List UInt8 :=
  encodeUIntLE 8 message.correlationId

def decode (bytes : List UInt8) : Option (HeartbeatMessage × List UInt8) := do
  let (correlationId, bytes) ← decodeUIntLE 8 bytes
  pure ({ correlationId }, bytes)

@[simp] theorem encode_length (message : HeartbeatMessage) : (encode message).length = 8 := by
  unfold encode
  simp only [encodeUIntLE_length]

theorem encode_length_pos (message : HeartbeatMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : HeartbeatMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end HeartbeatMessage

/-- Test Request Message: 8 bytes -/
structure TestRequestMessage where
  correlationId : BitVec 64
  deriving DecidableEq, Repr

namespace TestRequestMessage

def encode (message : TestRequestMessage) : List UInt8 :=
  encodeUIntLE 8 message.correlationId

def decode (bytes : List UInt8) : Option (TestRequestMessage × List UInt8) := do
  let (correlationId, bytes) ← decodeUIntLE 8 bytes
  pure ({ correlationId }, bytes)

@[simp] theorem encode_length (message : TestRequestMessage) : (encode message).length = 8 := by
  unfold encode
  simp only [encodeUIntLE_length]

theorem encode_length_pos (message : TestRequestMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : TestRequestMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end TestRequestMessage

/-- Resend Request Message: 16 bytes -/
structure ResendRequestMessage where
  fromSequenceNumber : BitVec 64
  toSequenceNumber : BitVec 64
  deriving DecidableEq, Repr

namespace ResendRequestMessage

def encode (message : ResendRequestMessage) : List UInt8 :=
  encodeUIntLE 8 message.fromSequenceNumber
    ++ (encodeUIntLE 8 message.toSequenceNumber)

def decode (bytes : List UInt8) : Option (ResendRequestMessage × List UInt8) := do
  let (fromSequenceNumber, bytes) ← decodeUIntLE 8 bytes
  let (toSequenceNumber, bytes) ← decodeUIntLE 8 bytes
  pure ({ fromSequenceNumber, toSequenceNumber }, bytes)

@[simp] theorem encode_length (message : ResendRequestMessage) : (encode message).length = 16 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length]

theorem encode_length_pos (message : ResendRequestMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : ResendRequestMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end ResendRequestMessage

/-- Gap Fill Message: 8 bytes -/
structure GapFillMessage where
  newSequenceNumber : BitVec 64
  deriving DecidableEq, Repr

namespace GapFillMessage

def encode (message : GapFillMessage) : List UInt8 :=
  encodeUIntLE 8 message.newSequenceNumber

def decode (bytes : List UInt8) : Option (GapFillMessage × List UInt8) := do
  let (newSequenceNumber, bytes) ← decodeUIntLE 8 bytes
  pure ({ newSequenceNumber }, bytes)

@[simp] theorem encode_length (message : GapFillMessage) : (encode message).length = 8 := by
  unfold encode
  simp only [encodeUIntLE_length]

theorem encode_length_pos (message : GapFillMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : GapFillMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end GapFillMessage

/-- Details -/
structure Details where
  detailsData : Bounded 1 UInt8
  deriving DecidableEq, Repr

namespace Details

def encode (message : Details) : List UInt8 :=
  encodeUInt 1 (BitVec.ofNat (8 * 1) message.detailsData.val.length)
    ++ (encodeMany Byte.encode message.detailsData.val)

def decode (bytes : List UInt8) : Option (Details × List UInt8) := do
  let (detailsLength, bytes) ← decodeUInt 1 bytes
  let (detailsData_, bytes) ← decodeMany Byte.decode detailsLength.toNat bytes
  if fits_detailsData : detailsData_.length < 256 ^ 1 then
    pure ({ detailsData := ⟨detailsData_, fits_detailsData⟩ }, bytes)
  else none

theorem encode_length_pos (message : Details) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUInt_length, List.length_append]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : Details) : (encode message).length ≤ 256 := by
  have bound_detailsData := message.detailsData.length_lt
  unfold encode
  simp only [List.length_append, encodeUInt_length, encodeMany_length_const Byte.encode 1 Byte.encode_length]
  omega

@[simp] theorem decode_encode (message : Details) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeMany_bounded 1 Byte.encode Byte.decode Byte.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.detailsData.length_lt]
  rfl

end Details

/-- Reject Message -/
structure RejectMessage where
  refSequenceNumber : BitVec 64
  reasonRejectReason : BitVec 8
  details : Details
  deriving DecidableEq, Repr

namespace RejectMessage

def encode (message : RejectMessage) : List UInt8 :=
  encodeUIntLE 8 message.refSequenceNumber
    ++ (encodeUInt 1 message.reasonRejectReason
    ++ (Details.encode message.details))

def decode (bytes : List UInt8) : Option (RejectMessage × List UInt8) := do
  let (refSequenceNumber, bytes) ← decodeUIntLE 8 bytes
  let (reasonRejectReason, bytes) ← decodeUInt 1 bytes
  let (details, bytes) ← Details.decode bytes
  pure ({ refSequenceNumber, reasonRejectReason, details }, bytes)

theorem encode_length_pos (message : RejectMessage) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUIntLE_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : RejectMessage) : (encode message).length ≤ 265 := by
  have bound_details := Details.encode_length_le message.details
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, encodeUIntLE_length, encodeUInt_length]
  omega

@[simp] theorem decode_encode (message : RejectMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [Details.decode_encode, some_bind]
  rfl

end RejectMessage

/-- Quantity: 9 bytes -/
structure Quantity where
  mantissa : BitVec 64
  exponent : BitVec 8
  deriving DecidableEq, Repr

namespace Quantity

def encode (message : Quantity) : List UInt8 :=
  encodeUIntLE 8 message.mantissa
    ++ (encodeUInt 1 message.exponent)

def decode (bytes : List UInt8) : Option (Quantity × List UInt8) := do
  let (mantissa, bytes) ← decodeUIntLE 8 bytes
  let (exponent, bytes) ← decodeUInt 1 bytes
  pure ({ mantissa, exponent }, bytes)

@[simp] theorem encode_length (message : Quantity) : (encode message).length = 9 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, encodeUInt_length]

theorem encode_length_pos (message : Quantity) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : Quantity) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end Quantity

/-- Show Qty: 9 bytes -/
structure ShowQty where
  mantissa : BitVec 64
  exponent : BitVec 8
  deriving DecidableEq, Repr

namespace ShowQty

def encode (message : ShowQty) : List UInt8 :=
  encodeUIntLE 8 message.mantissa
    ++ (encodeUInt 1 message.exponent)

def decode (bytes : List UInt8) : Option (ShowQty × List UInt8) := do
  let (mantissa, bytes) ← decodeUIntLE 8 bytes
  let (exponent, bytes) ← decodeUInt 1 bytes
  pure ({ mantissa, exponent }, bytes)

@[simp] theorem encode_length (message : ShowQty) : (encode message).length = 9 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, encodeUInt_length]

theorem encode_length_pos (message : ShowQty) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : ShowQty) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end ShowQty

/-- New Order Request Message: 63 bytes -/
structure NewOrderRequestMessage where
  clientOrderId : BitVec 64
  correlationId : BitVec 64
  instrumentId : BitVec 64
  price : BitVec 64
  quantity : Quantity
  showQty : ShowQty
  selfMatchPreventionId : BitVec 64
  side : BitVec 8
  timeInForce : BitVec 8
  flagsOrderFlags : BitVec 16
  selfTradingMode : BitVec 8
  deriving DecidableEq, Repr

namespace NewOrderRequestMessage

def encode (message : NewOrderRequestMessage) : List UInt8 :=
  encodeUIntLE 8 message.clientOrderId
    ++ (encodeUIntLE 8 message.correlationId
    ++ (encodeUIntLE 8 message.instrumentId
    ++ (encodeUIntLE 8 message.price
    ++ (Quantity.encode message.quantity
    ++ (ShowQty.encode message.showQty
    ++ (encodeUIntLE 8 message.selfMatchPreventionId
    ++ (encodeUInt 1 message.side
    ++ (encodeUInt 1 message.timeInForce
    ++ (encodeUIntLE 2 message.flagsOrderFlags
    ++ (encodeUInt 1 message.selfTradingMode))))))))))

def decode (bytes : List UInt8) : Option (NewOrderRequestMessage × List UInt8) := do
  let (clientOrderId, bytes) ← decodeUIntLE 8 bytes
  let (correlationId, bytes) ← decodeUIntLE 8 bytes
  let (instrumentId, bytes) ← decodeUIntLE 8 bytes
  let (price, bytes) ← decodeUIntLE 8 bytes
  let (quantity, bytes) ← Quantity.decode bytes
  let (showQty, bytes) ← ShowQty.decode bytes
  let (selfMatchPreventionId, bytes) ← decodeUIntLE 8 bytes
  let (side, bytes) ← decodeUInt 1 bytes
  let (timeInForce, bytes) ← decodeUInt 1 bytes
  let (flagsOrderFlags, bytes) ← decodeUIntLE 2 bytes
  let (selfTradingMode, bytes) ← decodeUInt 1 bytes
  pure ({ clientOrderId, correlationId, instrumentId, price, quantity, showQty, selfMatchPreventionId, side, timeInForce, flagsOrderFlags, selfTradingMode }, bytes)

@[simp] theorem encode_length (message : NewOrderRequestMessage) : (encode message).length = 63 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Quantity.encode_length, ShowQty.encode_length, encodeUInt_length]

theorem encode_length_pos (message : NewOrderRequestMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : NewOrderRequestMessage) (rest : List UInt8) :
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
  rw [List.append_assoc, Quantity.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, ShowQty.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end NewOrderRequestMessage

/-- Amend Order Request Message: 52 bytes -/
structure AmendOrderRequestMessage where
  clientOrderId : BitVec 64
  correlationId : BitVec 64
  instrumentId : BitVec 64
  price : BitVec 64
  quantity : Quantity
  showQty : ShowQty
  flagsReplaceOrderFlags : BitVec 16
  deriving DecidableEq, Repr

namespace AmendOrderRequestMessage

def encode (message : AmendOrderRequestMessage) : List UInt8 :=
  encodeUIntLE 8 message.clientOrderId
    ++ (encodeUIntLE 8 message.correlationId
    ++ (encodeUIntLE 8 message.instrumentId
    ++ (encodeUIntLE 8 message.price
    ++ (Quantity.encode message.quantity
    ++ (ShowQty.encode message.showQty
    ++ (encodeUIntLE 2 message.flagsReplaceOrderFlags))))))

def decode (bytes : List UInt8) : Option (AmendOrderRequestMessage × List UInt8) := do
  let (clientOrderId, bytes) ← decodeUIntLE 8 bytes
  let (correlationId, bytes) ← decodeUIntLE 8 bytes
  let (instrumentId, bytes) ← decodeUIntLE 8 bytes
  let (price, bytes) ← decodeUIntLE 8 bytes
  let (quantity, bytes) ← Quantity.decode bytes
  let (showQty, bytes) ← ShowQty.decode bytes
  let (flagsReplaceOrderFlags, bytes) ← decodeUIntLE 2 bytes
  pure ({ clientOrderId, correlationId, instrumentId, price, quantity, showQty, flagsReplaceOrderFlags }, bytes)

@[simp] theorem encode_length (message : AmendOrderRequestMessage) : (encode message).length = 52 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Quantity.encode_length, ShowQty.encode_length]

theorem encode_length_pos (message : AmendOrderRequestMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : AmendOrderRequestMessage) (rest : List UInt8) :
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
  rw [List.append_assoc, Quantity.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, ShowQty.decode_encode, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end AmendOrderRequestMessage

/-- Cancel Order Request Message: 24 bytes -/
structure CancelOrderRequestMessage where
  clientOrderId : BitVec 64
  correlationId : BitVec 64
  instrumentId : BitVec 64
  deriving DecidableEq, Repr

namespace CancelOrderRequestMessage

def encode (message : CancelOrderRequestMessage) : List UInt8 :=
  encodeUIntLE 8 message.clientOrderId
    ++ (encodeUIntLE 8 message.correlationId
    ++ (encodeUIntLE 8 message.instrumentId))

def decode (bytes : List UInt8) : Option (CancelOrderRequestMessage × List UInt8) := do
  let (clientOrderId, bytes) ← decodeUIntLE 8 bytes
  let (correlationId, bytes) ← decodeUIntLE 8 bytes
  let (instrumentId, bytes) ← decodeUIntLE 8 bytes
  pure ({ clientOrderId, correlationId, instrumentId }, bytes)

@[simp] theorem encode_length (message : CancelOrderRequestMessage) : (encode message).length = 24 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length]

theorem encode_length_pos (message : CancelOrderRequestMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : CancelOrderRequestMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end CancelOrderRequestMessage

/-- Bid Qty: 9 bytes -/
structure BidQty where
  mantissa : BitVec 64
  exponent : BitVec 8
  deriving DecidableEq, Repr

namespace BidQty

def encode (message : BidQty) : List UInt8 :=
  encodeUIntLE 8 message.mantissa
    ++ (encodeUInt 1 message.exponent)

def decode (bytes : List UInt8) : Option (BidQty × List UInt8) := do
  let (mantissa, bytes) ← decodeUIntLE 8 bytes
  let (exponent, bytes) ← decodeUInt 1 bytes
  pure ({ mantissa, exponent }, bytes)

@[simp] theorem encode_length (message : BidQty) : (encode message).length = 9 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, encodeUInt_length]

theorem encode_length_pos (message : BidQty) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : BidQty) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end BidQty

/-- Ask Qty: 9 bytes -/
structure AskQty where
  mantissa : BitVec 64
  exponent : BitVec 8
  deriving DecidableEq, Repr

namespace AskQty

def encode (message : AskQty) : List UInt8 :=
  encodeUIntLE 8 message.mantissa
    ++ (encodeUInt 1 message.exponent)

def decode (bytes : List UInt8) : Option (AskQty × List UInt8) := do
  let (mantissa, bytes) ← decodeUIntLE 8 bytes
  let (exponent, bytes) ← decodeUInt 1 bytes
  pure ({ mantissa, exponent }, bytes)

@[simp] theorem encode_length (message : AskQty) : (encode message).length = 9 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, encodeUInt_length]

theorem encode_length_pos (message : AskQty) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : AskQty) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end AskQty

/-- Mass Quote Request Message quotes Group: 46 bytes -/
structure MassQuoteRequestMessageQuotesGroup where
  instrumentId : BitVec 64
  bidPriceOptional : BitVec 64
  askPriceOptional : BitVec 64
  bidQty : BidQty
  askQty : AskQty
  bidFlags : BitVec 16
  askFlags : BitVec 16
  deriving DecidableEq, Repr

namespace MassQuoteRequestMessageQuotesGroup

def encode (message : MassQuoteRequestMessageQuotesGroup) : List UInt8 :=
  encodeUIntLE 8 message.instrumentId
    ++ (encodeUIntLE 8 message.bidPriceOptional
    ++ (encodeUIntLE 8 message.askPriceOptional
    ++ (BidQty.encode message.bidQty
    ++ (AskQty.encode message.askQty
    ++ (encodeUIntLE 2 message.bidFlags
    ++ (encodeUIntLE 2 message.askFlags))))))

def decode (bytes : List UInt8) : Option (MassQuoteRequestMessageQuotesGroup × List UInt8) := do
  let (instrumentId, bytes) ← decodeUIntLE 8 bytes
  let (bidPriceOptional, bytes) ← decodeUIntLE 8 bytes
  let (askPriceOptional, bytes) ← decodeUIntLE 8 bytes
  let (bidQty, bytes) ← BidQty.decode bytes
  let (askQty, bytes) ← AskQty.decode bytes
  let (bidFlags, bytes) ← decodeUIntLE 2 bytes
  let (askFlags, bytes) ← decodeUIntLE 2 bytes
  pure ({ instrumentId, bidPriceOptional, askPriceOptional, bidQty, askQty, bidFlags, askFlags }, bytes)

@[simp] theorem encode_length (message : MassQuoteRequestMessageQuotesGroup) : (encode message).length = 46 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, BidQty.encode_length, AskQty.encode_length]

theorem encode_length_pos (message : MassQuoteRequestMessageQuotesGroup) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : MassQuoteRequestMessageQuotesGroup) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, BidQty.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, AskQty.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end MassQuoteRequestMessageQuotesGroup

/-- Mass Quote Request Message quotes Groups -/
structure MassQuoteRequestMessageQuotesGroups where
  blockLength : BitVec 16
  massQuoteRequestMessageQuotesGroup : Bounded 2 MassQuoteRequestMessageQuotesGroup
  deriving DecidableEq, Repr

namespace MassQuoteRequestMessageQuotesGroups

def encode (message : MassQuoteRequestMessageQuotesGroups) : List UInt8 :=
  encodeUIntLE 2 message.blockLength
    ++ (encodeUIntLE 2 (BitVec.ofNat (8 * 2) message.massQuoteRequestMessageQuotesGroup.val.length)
    ++ (encodeMany MassQuoteRequestMessageQuotesGroup.encode message.massQuoteRequestMessageQuotesGroup.val))

def decode (bytes : List UInt8) : Option (MassQuoteRequestMessageQuotesGroups × List UInt8) := do
  let (blockLength, bytes) ← decodeUIntLE 2 bytes
  let (numInGroup, bytes) ← decodeUIntLE 2 bytes
  let (massQuoteRequestMessageQuotesGroup_, bytes) ← decodeMany MassQuoteRequestMessageQuotesGroup.decode numInGroup.toNat bytes
  if fits_massQuoteRequestMessageQuotesGroup : massQuoteRequestMessageQuotesGroup_.length < 256 ^ 2 then
    pure ({ blockLength, massQuoteRequestMessageQuotesGroup := ⟨massQuoteRequestMessageQuotesGroup_, fits_massQuoteRequestMessageQuotesGroup⟩ }, bytes)
  else none

theorem encode_length_pos (message : MassQuoteRequestMessageQuotesGroups) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUIntLE_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : MassQuoteRequestMessageQuotesGroups) : (encode message).length ≤ 3014614 := by
  have bound_massQuoteRequestMessageQuotesGroup := message.massQuoteRequestMessageQuotesGroup.length_lt
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, encodeUIntLE_length, encodeMany_length_const MassQuoteRequestMessageQuotesGroup.encode 46 MassQuoteRequestMessageQuotesGroup.encode_length]
  omega

@[simp] theorem decode_encode (message : MassQuoteRequestMessageQuotesGroups) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeMany_bounded 2 MassQuoteRequestMessageQuotesGroup.encode MassQuoteRequestMessageQuotesGroup.decode MassQuoteRequestMessageQuotesGroup.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.massQuoteRequestMessageQuotesGroup.length_lt]
  rfl

end MassQuoteRequestMessageQuotesGroups

/-- Mass Quote Request Message -/
structure MassQuoteRequestMessage where
  quoteId : BitVec 64
  correlationId : BitVec 64
  mmpGroupId : BitVec 64
  selfMatchPreventionId : BitVec 64
  flagsMassQuoteFlags : BitVec 8
  massQuoteRequestMessageQuotesGroups : MassQuoteRequestMessageQuotesGroups
  deriving DecidableEq, Repr

namespace MassQuoteRequestMessage

def encode (message : MassQuoteRequestMessage) : List UInt8 :=
  encodeUIntLE 8 message.quoteId
    ++ (encodeUIntLE 8 message.correlationId
    ++ (encodeUIntLE 8 message.mmpGroupId
    ++ (encodeUIntLE 8 message.selfMatchPreventionId
    ++ (encodeUIntLE 1 message.flagsMassQuoteFlags
    ++ (MassQuoteRequestMessageQuotesGroups.encode message.massQuoteRequestMessageQuotesGroups)))))

def decode (bytes : List UInt8) : Option (MassQuoteRequestMessage × List UInt8) := do
  let (quoteId, bytes) ← decodeUIntLE 8 bytes
  let (correlationId, bytes) ← decodeUIntLE 8 bytes
  let (mmpGroupId, bytes) ← decodeUIntLE 8 bytes
  let (selfMatchPreventionId, bytes) ← decodeUIntLE 8 bytes
  let (flagsMassQuoteFlags, bytes) ← decodeUIntLE 1 bytes
  let (massQuoteRequestMessageQuotesGroups, bytes) ← MassQuoteRequestMessageQuotesGroups.decode bytes
  pure ({ quoteId, correlationId, mmpGroupId, selfMatchPreventionId, flagsMassQuoteFlags, massQuoteRequestMessageQuotesGroups }, bytes)

theorem encode_length_pos (message : MassQuoteRequestMessage) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUIntLE_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : MassQuoteRequestMessage) : (encode message).length ≤ 3014647 := by
  have bound_massQuoteRequestMessageQuotesGroups := MassQuoteRequestMessageQuotesGroups.encode_length_le message.massQuoteRequestMessageQuotesGroups
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, encodeUIntLE_length]
  omega

@[simp] theorem decode_encode (message : MassQuoteRequestMessage) (rest : List UInt8) :
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
  rw [MassQuoteRequestMessageQuotesGroups.decode_encode, some_bind]
  rfl

end MassQuoteRequestMessage

/-- Mass Cancel Request Message: 26 bytes -/
structure MassCancelRequestMessage where
  correlationId : BitVec 64
  currencyPairId : BitVec 64
  instrumentIdOptional : BitVec 64
  productType : BitVec 8
  side : BitVec 8
  deriving DecidableEq, Repr

namespace MassCancelRequestMessage

def encode (message : MassCancelRequestMessage) : List UInt8 :=
  encodeUIntLE 8 message.correlationId
    ++ (encodeUIntLE 8 message.currencyPairId
    ++ (encodeUIntLE 8 message.instrumentIdOptional
    ++ (encodeUInt 1 message.productType
    ++ (encodeUInt 1 message.side))))

def decode (bytes : List UInt8) : Option (MassCancelRequestMessage × List UInt8) := do
  let (correlationId, bytes) ← decodeUIntLE 8 bytes
  let (currencyPairId, bytes) ← decodeUIntLE 8 bytes
  let (instrumentIdOptional, bytes) ← decodeUIntLE 8 bytes
  let (productType, bytes) ← decodeUInt 1 bytes
  let (side, bytes) ← decodeUInt 1 bytes
  pure ({ correlationId, currencyPairId, instrumentIdOptional, productType, side }, bytes)

@[simp] theorem encode_length (message : MassCancelRequestMessage) : (encode message).length = 26 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, encodeUInt_length]

theorem encode_length_pos (message : MassCancelRequestMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : MassCancelRequestMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end MassCancelRequestMessage

/-- Mass Quote Cancel Request Message: 17 bytes -/
structure MassQuoteCancelRequestMessage where
  correlationId : BitVec 64
  mmpGroupId : BitVec 64
  side : BitVec 8
  deriving DecidableEq, Repr

namespace MassQuoteCancelRequestMessage

def encode (message : MassQuoteCancelRequestMessage) : List UInt8 :=
  encodeUIntLE 8 message.correlationId
    ++ (encodeUIntLE 8 message.mmpGroupId
    ++ (encodeUInt 1 message.side))

def decode (bytes : List UInt8) : Option (MassQuoteCancelRequestMessage × List UInt8) := do
  let (correlationId, bytes) ← decodeUIntLE 8 bytes
  let (mmpGroupId, bytes) ← decodeUIntLE 8 bytes
  let (side, bytes) ← decodeUInt 1 bytes
  pure ({ correlationId, mmpGroupId, side }, bytes)

@[simp] theorem encode_length (message : MassQuoteCancelRequestMessage) : (encode message).length = 17 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, encodeUInt_length]

theorem encode_length_pos (message : MassQuoteCancelRequestMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : MassQuoteCancelRequestMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end MassQuoteCancelRequestMessage

/-- Total Filled: 9 bytes -/
structure TotalFilled where
  mantissa : BitVec 64
  exponent : BitVec 8
  deriving DecidableEq, Repr

namespace TotalFilled

def encode (message : TotalFilled) : List UInt8 :=
  encodeUIntLE 8 message.mantissa
    ++ (encodeUInt 1 message.exponent)

def decode (bytes : List UInt8) : Option (TotalFilled × List UInt8) := do
  let (mantissa, bytes) ← decodeUIntLE 8 bytes
  let (exponent, bytes) ← decodeUInt 1 bytes
  pure ({ mantissa, exponent }, bytes)

@[simp] theorem encode_length (message : TotalFilled) : (encode message).length = 9 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, encodeUInt_length]

theorem encode_length_pos (message : TotalFilled) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : TotalFilled) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end TotalFilled

/-- Visible Qty: 9 bytes -/
structure VisibleQty where
  mantissa : BitVec 64
  exponent : BitVec 8
  deriving DecidableEq, Repr

namespace VisibleQty

def encode (message : VisibleQty) : List UInt8 :=
  encodeUIntLE 8 message.mantissa
    ++ (encodeUInt 1 message.exponent)

def decode (bytes : List UInt8) : Option (VisibleQty × List UInt8) := do
  let (mantissa, bytes) ← decodeUIntLE 8 bytes
  let (exponent, bytes) ← decodeUInt 1 bytes
  pure ({ mantissa, exponent }, bytes)

@[simp] theorem encode_length (message : VisibleQty) : (encode message).length = 9 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, encodeUInt_length]

theorem encode_length_pos (message : VisibleQty) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : VisibleQty) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end VisibleQty

/-- Fill Qty: 9 bytes -/
structure FillQty where
  mantissa : BitVec 64
  exponent : BitVec 8
  deriving DecidableEq, Repr

namespace FillQty

def encode (message : FillQty) : List UInt8 :=
  encodeUIntLE 8 message.mantissa
    ++ (encodeUInt 1 message.exponent)

def decode (bytes : List UInt8) : Option (FillQty × List UInt8) := do
  let (mantissa, bytes) ← decodeUIntLE 8 bytes
  let (exponent, bytes) ← decodeUInt 1 bytes
  pure ({ mantissa, exponent }, bytes)

@[simp] theorem encode_length (message : FillQty) : (encode message).length = 9 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, encodeUInt_length]

theorem encode_length_pos (message : FillQty) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : FillQty) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end FillQty

/-- New Order Response Message fills Group: 25 bytes -/
structure NewOrderResponseMessageFillsGroup where
  matchId : BitVec 64
  fillPrice : BitVec 64
  fillQty : FillQty
  deriving DecidableEq, Repr

namespace NewOrderResponseMessageFillsGroup

def encode (message : NewOrderResponseMessageFillsGroup) : List UInt8 :=
  encodeUIntLE 8 message.matchId
    ++ (encodeUIntLE 8 message.fillPrice
    ++ (FillQty.encode message.fillQty))

def decode (bytes : List UInt8) : Option (NewOrderResponseMessageFillsGroup × List UInt8) := do
  let (matchId, bytes) ← decodeUIntLE 8 bytes
  let (fillPrice, bytes) ← decodeUIntLE 8 bytes
  let (fillQty, bytes) ← FillQty.decode bytes
  pure ({ matchId, fillPrice, fillQty }, bytes)

@[simp] theorem encode_length (message : NewOrderResponseMessageFillsGroup) : (encode message).length = 25 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, FillQty.encode_length]

theorem encode_length_pos (message : NewOrderResponseMessageFillsGroup) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : NewOrderResponseMessageFillsGroup) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [FillQty.decode_encode, some_bind]
  rfl

end NewOrderResponseMessageFillsGroup

/-- New Order Response Message fills Groups -/
structure NewOrderResponseMessageFillsGroups where
  blockLength : BitVec 16
  newOrderResponseMessageFillsGroup : Bounded 2 NewOrderResponseMessageFillsGroup
  deriving DecidableEq, Repr

namespace NewOrderResponseMessageFillsGroups

def encode (message : NewOrderResponseMessageFillsGroups) : List UInt8 :=
  encodeUIntLE 2 message.blockLength
    ++ (encodeUIntLE 2 (BitVec.ofNat (8 * 2) message.newOrderResponseMessageFillsGroup.val.length)
    ++ (encodeMany NewOrderResponseMessageFillsGroup.encode message.newOrderResponseMessageFillsGroup.val))

def decode (bytes : List UInt8) : Option (NewOrderResponseMessageFillsGroups × List UInt8) := do
  let (blockLength, bytes) ← decodeUIntLE 2 bytes
  let (numInGroup, bytes) ← decodeUIntLE 2 bytes
  let (newOrderResponseMessageFillsGroup_, bytes) ← decodeMany NewOrderResponseMessageFillsGroup.decode numInGroup.toNat bytes
  if fits_newOrderResponseMessageFillsGroup : newOrderResponseMessageFillsGroup_.length < 256 ^ 2 then
    pure ({ blockLength, newOrderResponseMessageFillsGroup := ⟨newOrderResponseMessageFillsGroup_, fits_newOrderResponseMessageFillsGroup⟩ }, bytes)
  else none

theorem encode_length_pos (message : NewOrderResponseMessageFillsGroups) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUIntLE_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : NewOrderResponseMessageFillsGroups) : (encode message).length ≤ 1638379 := by
  have bound_newOrderResponseMessageFillsGroup := message.newOrderResponseMessageFillsGroup.length_lt
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, encodeUIntLE_length, encodeMany_length_const NewOrderResponseMessageFillsGroup.encode 25 NewOrderResponseMessageFillsGroup.encode_length]
  omega

@[simp] theorem decode_encode (message : NewOrderResponseMessageFillsGroups) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeMany_bounded 2 NewOrderResponseMessageFillsGroup.encode NewOrderResponseMessageFillsGroup.decode NewOrderResponseMessageFillsGroup.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.newOrderResponseMessageFillsGroup.length_lt]
  rfl

end NewOrderResponseMessageFillsGroups

/-- New Order Response Message legs Group: 34 bytes -/
structure NewOrderResponseMessageLegsGroup where
  matchId : BitVec 64
  fillId : BitVec 64
  fillPrice : BitVec 64
  fillQty : FillQty
  legSide : BitVec 8
  deriving DecidableEq, Repr

namespace NewOrderResponseMessageLegsGroup

def encode (message : NewOrderResponseMessageLegsGroup) : List UInt8 :=
  encodeUIntLE 8 message.matchId
    ++ (encodeUIntLE 8 message.fillId
    ++ (encodeUIntLE 8 message.fillPrice
    ++ (FillQty.encode message.fillQty
    ++ (encodeUInt 1 message.legSide))))

def decode (bytes : List UInt8) : Option (NewOrderResponseMessageLegsGroup × List UInt8) := do
  let (matchId, bytes) ← decodeUIntLE 8 bytes
  let (fillId, bytes) ← decodeUIntLE 8 bytes
  let (fillPrice, bytes) ← decodeUIntLE 8 bytes
  let (fillQty, bytes) ← FillQty.decode bytes
  let (legSide, bytes) ← decodeUInt 1 bytes
  pure ({ matchId, fillId, fillPrice, fillQty, legSide }, bytes)

@[simp] theorem encode_length (message : NewOrderResponseMessageLegsGroup) : (encode message).length = 34 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, FillQty.encode_length, encodeUInt_length]

theorem encode_length_pos (message : NewOrderResponseMessageLegsGroup) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : NewOrderResponseMessageLegsGroup) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, FillQty.decode_encode, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end NewOrderResponseMessageLegsGroup

/-- New Order Response Message legs Groups -/
structure NewOrderResponseMessageLegsGroups where
  blockLength : BitVec 16
  newOrderResponseMessageLegsGroup : Bounded 2 NewOrderResponseMessageLegsGroup
  deriving DecidableEq, Repr

namespace NewOrderResponseMessageLegsGroups

def encode (message : NewOrderResponseMessageLegsGroups) : List UInt8 :=
  encodeUIntLE 2 message.blockLength
    ++ (encodeUIntLE 2 (BitVec.ofNat (8 * 2) message.newOrderResponseMessageLegsGroup.val.length)
    ++ (encodeMany NewOrderResponseMessageLegsGroup.encode message.newOrderResponseMessageLegsGroup.val))

def decode (bytes : List UInt8) : Option (NewOrderResponseMessageLegsGroups × List UInt8) := do
  let (blockLength, bytes) ← decodeUIntLE 2 bytes
  let (numInGroup, bytes) ← decodeUIntLE 2 bytes
  let (newOrderResponseMessageLegsGroup_, bytes) ← decodeMany NewOrderResponseMessageLegsGroup.decode numInGroup.toNat bytes
  if fits_newOrderResponseMessageLegsGroup : newOrderResponseMessageLegsGroup_.length < 256 ^ 2 then
    pure ({ blockLength, newOrderResponseMessageLegsGroup := ⟨newOrderResponseMessageLegsGroup_, fits_newOrderResponseMessageLegsGroup⟩ }, bytes)
  else none

theorem encode_length_pos (message : NewOrderResponseMessageLegsGroups) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUIntLE_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : NewOrderResponseMessageLegsGroups) : (encode message).length ≤ 2228194 := by
  have bound_newOrderResponseMessageLegsGroup := message.newOrderResponseMessageLegsGroup.length_lt
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, encodeUIntLE_length, encodeMany_length_const NewOrderResponseMessageLegsGroup.encode 34 NewOrderResponseMessageLegsGroup.encode_length]
  omega

@[simp] theorem decode_encode (message : NewOrderResponseMessageLegsGroups) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeMany_bounded 2 NewOrderResponseMessageLegsGroup.encode NewOrderResponseMessageLegsGroup.decode NewOrderResponseMessageLegsGroup.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.newOrderResponseMessageLegsGroup.length_lt]
  rfl

end NewOrderResponseMessageLegsGroups

/-- New Order Response Message -/
structure NewOrderResponseMessage where
  timestamp : BitVec 64
  execId : BitVec 64
  clientOrderId : BitVec 64
  correlationId : BitVec 64
  orderId : BitVec 64
  instrumentId : BitVec 64
  price : BitVec 64
  quantity : Quantity
  totalFilled : TotalFilled
  visibleQty : VisibleQty
  receiveTime : BitVec 64
  side : BitVec 8
  status : BitVec 8
  cancelReason : BitVec 8
  newOrderResponseMessageFillsGroups : NewOrderResponseMessageFillsGroups
  newOrderResponseMessageLegsGroups : NewOrderResponseMessageLegsGroups
  deriving DecidableEq, Repr

namespace NewOrderResponseMessage

def encode (message : NewOrderResponseMessage) : List UInt8 :=
  encodeUIntLE 8 message.timestamp
    ++ (encodeUIntLE 8 message.execId
    ++ (encodeUIntLE 8 message.clientOrderId
    ++ (encodeUIntLE 8 message.correlationId
    ++ (encodeUIntLE 8 message.orderId
    ++ (encodeUIntLE 8 message.instrumentId
    ++ (encodeUIntLE 8 message.price
    ++ (Quantity.encode message.quantity
    ++ (TotalFilled.encode message.totalFilled
    ++ (VisibleQty.encode message.visibleQty
    ++ (encodeUIntLE 8 message.receiveTime
    ++ (encodeUInt 1 message.side
    ++ (encodeUInt 1 message.status
    ++ (encodeUInt 1 message.cancelReason
    ++ (NewOrderResponseMessageFillsGroups.encode message.newOrderResponseMessageFillsGroups
    ++ (NewOrderResponseMessageLegsGroups.encode message.newOrderResponseMessageLegsGroups)))))))))))))))

def decode (bytes : List UInt8) : Option (NewOrderResponseMessage × List UInt8) := do
  let (timestamp, bytes) ← decodeUIntLE 8 bytes
  let (execId, bytes) ← decodeUIntLE 8 bytes
  let (clientOrderId, bytes) ← decodeUIntLE 8 bytes
  let (correlationId, bytes) ← decodeUIntLE 8 bytes
  let (orderId, bytes) ← decodeUIntLE 8 bytes
  let (instrumentId, bytes) ← decodeUIntLE 8 bytes
  let (price, bytes) ← decodeUIntLE 8 bytes
  let (quantity, bytes) ← Quantity.decode bytes
  let (totalFilled, bytes) ← TotalFilled.decode bytes
  let (visibleQty, bytes) ← VisibleQty.decode bytes
  let (receiveTime, bytes) ← decodeUIntLE 8 bytes
  let (side, bytes) ← decodeUInt 1 bytes
  let (status, bytes) ← decodeUInt 1 bytes
  let (cancelReason, bytes) ← decodeUInt 1 bytes
  let (newOrderResponseMessageFillsGroups, bytes) ← NewOrderResponseMessageFillsGroups.decode bytes
  let (newOrderResponseMessageLegsGroups, bytes) ← NewOrderResponseMessageLegsGroups.decode bytes
  pure ({ timestamp, execId, clientOrderId, correlationId, orderId, instrumentId, price, quantity, totalFilled, visibleQty, receiveTime, side, status, cancelReason, newOrderResponseMessageFillsGroups, newOrderResponseMessageLegsGroups }, bytes)

theorem encode_length_pos (message : NewOrderResponseMessage) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUIntLE_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : NewOrderResponseMessage) : (encode message).length ≤ 3866667 := by
  have bound_newOrderResponseMessageFillsGroups := NewOrderResponseMessageFillsGroups.encode_length_le message.newOrderResponseMessageFillsGroups
  have bound_newOrderResponseMessageLegsGroups := NewOrderResponseMessageLegsGroups.encode_length_le message.newOrderResponseMessageLegsGroups
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, encodeUIntLE_length, Quantity.encode_length, TotalFilled.encode_length, VisibleQty.encode_length, encodeUInt_length]
  omega

@[simp] theorem decode_encode (message : NewOrderResponseMessage) (rest : List UInt8) :
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
  rw [List.append_assoc, Quantity.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, TotalFilled.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, VisibleQty.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, NewOrderResponseMessageFillsGroups.decode_encode, some_bind]
  dsimp only
  rw [NewOrderResponseMessageLegsGroups.decode_encode, some_bind]
  rfl

end NewOrderResponseMessage

/-- New Order Reject Message -/
structure NewOrderRejectMessage where
  timestamp : BitVec 64
  execId : BitVec 64
  clientOrderId : BitVec 64
  correlationId : BitVec 64
  orderId : BitVec 64
  instrumentId : BitVec 64
  reasonOrderRejectReason : BitVec 8
  details : Details
  deriving DecidableEq, Repr

namespace NewOrderRejectMessage

def encode (message : NewOrderRejectMessage) : List UInt8 :=
  encodeUIntLE 8 message.timestamp
    ++ (encodeUIntLE 8 message.execId
    ++ (encodeUIntLE 8 message.clientOrderId
    ++ (encodeUIntLE 8 message.correlationId
    ++ (encodeUIntLE 8 message.orderId
    ++ (encodeUIntLE 8 message.instrumentId
    ++ (encodeUInt 1 message.reasonOrderRejectReason
    ++ (Details.encode message.details)))))))

def decode (bytes : List UInt8) : Option (NewOrderRejectMessage × List UInt8) := do
  let (timestamp, bytes) ← decodeUIntLE 8 bytes
  let (execId, bytes) ← decodeUIntLE 8 bytes
  let (clientOrderId, bytes) ← decodeUIntLE 8 bytes
  let (correlationId, bytes) ← decodeUIntLE 8 bytes
  let (orderId, bytes) ← decodeUIntLE 8 bytes
  let (instrumentId, bytes) ← decodeUIntLE 8 bytes
  let (reasonOrderRejectReason, bytes) ← decodeUInt 1 bytes
  let (details, bytes) ← Details.decode bytes
  pure ({ timestamp, execId, clientOrderId, correlationId, orderId, instrumentId, reasonOrderRejectReason, details }, bytes)

theorem encode_length_pos (message : NewOrderRejectMessage) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUIntLE_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : NewOrderRejectMessage) : (encode message).length ≤ 305 := by
  have bound_details := Details.encode_length_le message.details
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, encodeUIntLE_length, encodeUInt_length]
  omega

@[simp] theorem decode_encode (message : NewOrderRejectMessage) (rest : List UInt8) :
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
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [Details.decode_encode, some_bind]
  rfl

end NewOrderRejectMessage

/-- Amend Order Response Message fills Group: 25 bytes -/
structure AmendOrderResponseMessageFillsGroup where
  matchId : BitVec 64
  fillPrice : BitVec 64
  fillQty : FillQty
  deriving DecidableEq, Repr

namespace AmendOrderResponseMessageFillsGroup

def encode (message : AmendOrderResponseMessageFillsGroup) : List UInt8 :=
  encodeUIntLE 8 message.matchId
    ++ (encodeUIntLE 8 message.fillPrice
    ++ (FillQty.encode message.fillQty))

def decode (bytes : List UInt8) : Option (AmendOrderResponseMessageFillsGroup × List UInt8) := do
  let (matchId, bytes) ← decodeUIntLE 8 bytes
  let (fillPrice, bytes) ← decodeUIntLE 8 bytes
  let (fillQty, bytes) ← FillQty.decode bytes
  pure ({ matchId, fillPrice, fillQty }, bytes)

@[simp] theorem encode_length (message : AmendOrderResponseMessageFillsGroup) : (encode message).length = 25 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, FillQty.encode_length]

theorem encode_length_pos (message : AmendOrderResponseMessageFillsGroup) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : AmendOrderResponseMessageFillsGroup) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [FillQty.decode_encode, some_bind]
  rfl

end AmendOrderResponseMessageFillsGroup

/-- Amend Order Response Message fills Groups -/
structure AmendOrderResponseMessageFillsGroups where
  blockLength : BitVec 16
  amendOrderResponseMessageFillsGroup : Bounded 2 AmendOrderResponseMessageFillsGroup
  deriving DecidableEq, Repr

namespace AmendOrderResponseMessageFillsGroups

def encode (message : AmendOrderResponseMessageFillsGroups) : List UInt8 :=
  encodeUIntLE 2 message.blockLength
    ++ (encodeUIntLE 2 (BitVec.ofNat (8 * 2) message.amendOrderResponseMessageFillsGroup.val.length)
    ++ (encodeMany AmendOrderResponseMessageFillsGroup.encode message.amendOrderResponseMessageFillsGroup.val))

def decode (bytes : List UInt8) : Option (AmendOrderResponseMessageFillsGroups × List UInt8) := do
  let (blockLength, bytes) ← decodeUIntLE 2 bytes
  let (numInGroup, bytes) ← decodeUIntLE 2 bytes
  let (amendOrderResponseMessageFillsGroup_, bytes) ← decodeMany AmendOrderResponseMessageFillsGroup.decode numInGroup.toNat bytes
  if fits_amendOrderResponseMessageFillsGroup : amendOrderResponseMessageFillsGroup_.length < 256 ^ 2 then
    pure ({ blockLength, amendOrderResponseMessageFillsGroup := ⟨amendOrderResponseMessageFillsGroup_, fits_amendOrderResponseMessageFillsGroup⟩ }, bytes)
  else none

theorem encode_length_pos (message : AmendOrderResponseMessageFillsGroups) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUIntLE_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : AmendOrderResponseMessageFillsGroups) : (encode message).length ≤ 1638379 := by
  have bound_amendOrderResponseMessageFillsGroup := message.amendOrderResponseMessageFillsGroup.length_lt
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, encodeUIntLE_length, encodeMany_length_const AmendOrderResponseMessageFillsGroup.encode 25 AmendOrderResponseMessageFillsGroup.encode_length]
  omega

@[simp] theorem decode_encode (message : AmendOrderResponseMessageFillsGroups) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeMany_bounded 2 AmendOrderResponseMessageFillsGroup.encode AmendOrderResponseMessageFillsGroup.decode AmendOrderResponseMessageFillsGroup.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.amendOrderResponseMessageFillsGroup.length_lt]
  rfl

end AmendOrderResponseMessageFillsGroups

/-- Amend Order Response Message legs Group: 34 bytes -/
structure AmendOrderResponseMessageLegsGroup where
  matchId : BitVec 64
  fillId : BitVec 64
  fillPrice : BitVec 64
  fillQty : FillQty
  legSide : BitVec 8
  deriving DecidableEq, Repr

namespace AmendOrderResponseMessageLegsGroup

def encode (message : AmendOrderResponseMessageLegsGroup) : List UInt8 :=
  encodeUIntLE 8 message.matchId
    ++ (encodeUIntLE 8 message.fillId
    ++ (encodeUIntLE 8 message.fillPrice
    ++ (FillQty.encode message.fillQty
    ++ (encodeUInt 1 message.legSide))))

def decode (bytes : List UInt8) : Option (AmendOrderResponseMessageLegsGroup × List UInt8) := do
  let (matchId, bytes) ← decodeUIntLE 8 bytes
  let (fillId, bytes) ← decodeUIntLE 8 bytes
  let (fillPrice, bytes) ← decodeUIntLE 8 bytes
  let (fillQty, bytes) ← FillQty.decode bytes
  let (legSide, bytes) ← decodeUInt 1 bytes
  pure ({ matchId, fillId, fillPrice, fillQty, legSide }, bytes)

@[simp] theorem encode_length (message : AmendOrderResponseMessageLegsGroup) : (encode message).length = 34 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, FillQty.encode_length, encodeUInt_length]

theorem encode_length_pos (message : AmendOrderResponseMessageLegsGroup) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : AmendOrderResponseMessageLegsGroup) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, FillQty.decode_encode, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end AmendOrderResponseMessageLegsGroup

/-- Amend Order Response Message legs Groups -/
structure AmendOrderResponseMessageLegsGroups where
  blockLength : BitVec 16
  amendOrderResponseMessageLegsGroup : Bounded 2 AmendOrderResponseMessageLegsGroup
  deriving DecidableEq, Repr

namespace AmendOrderResponseMessageLegsGroups

def encode (message : AmendOrderResponseMessageLegsGroups) : List UInt8 :=
  encodeUIntLE 2 message.blockLength
    ++ (encodeUIntLE 2 (BitVec.ofNat (8 * 2) message.amendOrderResponseMessageLegsGroup.val.length)
    ++ (encodeMany AmendOrderResponseMessageLegsGroup.encode message.amendOrderResponseMessageLegsGroup.val))

def decode (bytes : List UInt8) : Option (AmendOrderResponseMessageLegsGroups × List UInt8) := do
  let (blockLength, bytes) ← decodeUIntLE 2 bytes
  let (numInGroup, bytes) ← decodeUIntLE 2 bytes
  let (amendOrderResponseMessageLegsGroup_, bytes) ← decodeMany AmendOrderResponseMessageLegsGroup.decode numInGroup.toNat bytes
  if fits_amendOrderResponseMessageLegsGroup : amendOrderResponseMessageLegsGroup_.length < 256 ^ 2 then
    pure ({ blockLength, amendOrderResponseMessageLegsGroup := ⟨amendOrderResponseMessageLegsGroup_, fits_amendOrderResponseMessageLegsGroup⟩ }, bytes)
  else none

theorem encode_length_pos (message : AmendOrderResponseMessageLegsGroups) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUIntLE_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : AmendOrderResponseMessageLegsGroups) : (encode message).length ≤ 2228194 := by
  have bound_amendOrderResponseMessageLegsGroup := message.amendOrderResponseMessageLegsGroup.length_lt
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, encodeUIntLE_length, encodeMany_length_const AmendOrderResponseMessageLegsGroup.encode 34 AmendOrderResponseMessageLegsGroup.encode_length]
  omega

@[simp] theorem decode_encode (message : AmendOrderResponseMessageLegsGroups) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeMany_bounded 2 AmendOrderResponseMessageLegsGroup.encode AmendOrderResponseMessageLegsGroup.decode AmendOrderResponseMessageLegsGroup.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.amendOrderResponseMessageLegsGroup.length_lt]
  rfl

end AmendOrderResponseMessageLegsGroups

/-- Amend Order Response Message -/
structure AmendOrderResponseMessage where
  timestamp : BitVec 64
  execId : BitVec 64
  clientOrderId : BitVec 64
  correlationId : BitVec 64
  orderId : BitVec 64
  instrumentId : BitVec 64
  price : BitVec 64
  quantity : Quantity
  totalFilled : TotalFilled
  visibleQty : VisibleQty
  receiveTime : BitVec 64
  status : BitVec 8
  cancelReason : BitVec 8
  amendOrderResponseMessageFillsGroups : AmendOrderResponseMessageFillsGroups
  amendOrderResponseMessageLegsGroups : AmendOrderResponseMessageLegsGroups
  deriving DecidableEq, Repr

namespace AmendOrderResponseMessage

def encode (message : AmendOrderResponseMessage) : List UInt8 :=
  encodeUIntLE 8 message.timestamp
    ++ (encodeUIntLE 8 message.execId
    ++ (encodeUIntLE 8 message.clientOrderId
    ++ (encodeUIntLE 8 message.correlationId
    ++ (encodeUIntLE 8 message.orderId
    ++ (encodeUIntLE 8 message.instrumentId
    ++ (encodeUIntLE 8 message.price
    ++ (Quantity.encode message.quantity
    ++ (TotalFilled.encode message.totalFilled
    ++ (VisibleQty.encode message.visibleQty
    ++ (encodeUIntLE 8 message.receiveTime
    ++ (encodeUInt 1 message.status
    ++ (encodeUInt 1 message.cancelReason
    ++ (AmendOrderResponseMessageFillsGroups.encode message.amendOrderResponseMessageFillsGroups
    ++ (AmendOrderResponseMessageLegsGroups.encode message.amendOrderResponseMessageLegsGroups))))))))))))))

def decode (bytes : List UInt8) : Option (AmendOrderResponseMessage × List UInt8) := do
  let (timestamp, bytes) ← decodeUIntLE 8 bytes
  let (execId, bytes) ← decodeUIntLE 8 bytes
  let (clientOrderId, bytes) ← decodeUIntLE 8 bytes
  let (correlationId, bytes) ← decodeUIntLE 8 bytes
  let (orderId, bytes) ← decodeUIntLE 8 bytes
  let (instrumentId, bytes) ← decodeUIntLE 8 bytes
  let (price, bytes) ← decodeUIntLE 8 bytes
  let (quantity, bytes) ← Quantity.decode bytes
  let (totalFilled, bytes) ← TotalFilled.decode bytes
  let (visibleQty, bytes) ← VisibleQty.decode bytes
  let (receiveTime, bytes) ← decodeUIntLE 8 bytes
  let (status, bytes) ← decodeUInt 1 bytes
  let (cancelReason, bytes) ← decodeUInt 1 bytes
  let (amendOrderResponseMessageFillsGroups, bytes) ← AmendOrderResponseMessageFillsGroups.decode bytes
  let (amendOrderResponseMessageLegsGroups, bytes) ← AmendOrderResponseMessageLegsGroups.decode bytes
  pure ({ timestamp, execId, clientOrderId, correlationId, orderId, instrumentId, price, quantity, totalFilled, visibleQty, receiveTime, status, cancelReason, amendOrderResponseMessageFillsGroups, amendOrderResponseMessageLegsGroups }, bytes)

theorem encode_length_pos (message : AmendOrderResponseMessage) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUIntLE_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : AmendOrderResponseMessage) : (encode message).length ≤ 3866666 := by
  have bound_amendOrderResponseMessageFillsGroups := AmendOrderResponseMessageFillsGroups.encode_length_le message.amendOrderResponseMessageFillsGroups
  have bound_amendOrderResponseMessageLegsGroups := AmendOrderResponseMessageLegsGroups.encode_length_le message.amendOrderResponseMessageLegsGroups
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, encodeUIntLE_length, Quantity.encode_length, TotalFilled.encode_length, VisibleQty.encode_length, encodeUInt_length]
  omega

@[simp] theorem decode_encode (message : AmendOrderResponseMessage) (rest : List UInt8) :
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
  rw [List.append_assoc, Quantity.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, TotalFilled.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, VisibleQty.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, AmendOrderResponseMessageFillsGroups.decode_encode, some_bind]
  dsimp only
  rw [AmendOrderResponseMessageLegsGroups.decode_encode, some_bind]
  rfl

end AmendOrderResponseMessage

/-- Amend Order Reject Message -/
structure AmendOrderRejectMessage where
  timestamp : BitVec 64
  execId : BitVec 64
  clientOrderId : BitVec 64
  correlationId : BitVec 64
  orderId : BitVec 64
  instrumentId : BitVec 64
  reasonOrderRejectReason : BitVec 8
  details : Details
  deriving DecidableEq, Repr

namespace AmendOrderRejectMessage

def encode (message : AmendOrderRejectMessage) : List UInt8 :=
  encodeUIntLE 8 message.timestamp
    ++ (encodeUIntLE 8 message.execId
    ++ (encodeUIntLE 8 message.clientOrderId
    ++ (encodeUIntLE 8 message.correlationId
    ++ (encodeUIntLE 8 message.orderId
    ++ (encodeUIntLE 8 message.instrumentId
    ++ (encodeUInt 1 message.reasonOrderRejectReason
    ++ (Details.encode message.details)))))))

def decode (bytes : List UInt8) : Option (AmendOrderRejectMessage × List UInt8) := do
  let (timestamp, bytes) ← decodeUIntLE 8 bytes
  let (execId, bytes) ← decodeUIntLE 8 bytes
  let (clientOrderId, bytes) ← decodeUIntLE 8 bytes
  let (correlationId, bytes) ← decodeUIntLE 8 bytes
  let (orderId, bytes) ← decodeUIntLE 8 bytes
  let (instrumentId, bytes) ← decodeUIntLE 8 bytes
  let (reasonOrderRejectReason, bytes) ← decodeUInt 1 bytes
  let (details, bytes) ← Details.decode bytes
  pure ({ timestamp, execId, clientOrderId, correlationId, orderId, instrumentId, reasonOrderRejectReason, details }, bytes)

theorem encode_length_pos (message : AmendOrderRejectMessage) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUIntLE_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : AmendOrderRejectMessage) : (encode message).length ≤ 305 := by
  have bound_details := Details.encode_length_le message.details
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, encodeUIntLE_length, encodeUInt_length]
  omega

@[simp] theorem decode_encode (message : AmendOrderRejectMessage) (rest : List UInt8) :
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
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [Details.decode_encode, some_bind]
  rfl

end AmendOrderRejectMessage

/-- Cancel Order Response Message: 56 bytes -/
structure CancelOrderResponseMessage where
  timestamp : BitVec 64
  execId : BitVec 64
  clientOrderId : BitVec 64
  correlationId : BitVec 64
  orderId : BitVec 64
  instrumentId : BitVec 64
  receiveTime : BitVec 64
  deriving DecidableEq, Repr

namespace CancelOrderResponseMessage

def encode (message : CancelOrderResponseMessage) : List UInt8 :=
  encodeUIntLE 8 message.timestamp
    ++ (encodeUIntLE 8 message.execId
    ++ (encodeUIntLE 8 message.clientOrderId
    ++ (encodeUIntLE 8 message.correlationId
    ++ (encodeUIntLE 8 message.orderId
    ++ (encodeUIntLE 8 message.instrumentId
    ++ (encodeUIntLE 8 message.receiveTime))))))

def decode (bytes : List UInt8) : Option (CancelOrderResponseMessage × List UInt8) := do
  let (timestamp, bytes) ← decodeUIntLE 8 bytes
  let (execId, bytes) ← decodeUIntLE 8 bytes
  let (clientOrderId, bytes) ← decodeUIntLE 8 bytes
  let (correlationId, bytes) ← decodeUIntLE 8 bytes
  let (orderId, bytes) ← decodeUIntLE 8 bytes
  let (instrumentId, bytes) ← decodeUIntLE 8 bytes
  let (receiveTime, bytes) ← decodeUIntLE 8 bytes
  pure ({ timestamp, execId, clientOrderId, correlationId, orderId, instrumentId, receiveTime }, bytes)

@[simp] theorem encode_length (message : CancelOrderResponseMessage) : (encode message).length = 56 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length]

theorem encode_length_pos (message : CancelOrderResponseMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : CancelOrderResponseMessage) (rest : List UInt8) :
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

end CancelOrderResponseMessage

/-- Cancel Order Reject Message -/
structure CancelOrderRejectMessage where
  timestamp : BitVec 64
  execId : BitVec 64
  clientOrderId : BitVec 64
  correlationId : BitVec 64
  orderIdOptional : BitVec 64
  instrumentId : BitVec 64
  reasonCancelOrderRejectReason : BitVec 8
  details : Details
  deriving DecidableEq, Repr

namespace CancelOrderRejectMessage

def encode (message : CancelOrderRejectMessage) : List UInt8 :=
  encodeUIntLE 8 message.timestamp
    ++ (encodeUIntLE 8 message.execId
    ++ (encodeUIntLE 8 message.clientOrderId
    ++ (encodeUIntLE 8 message.correlationId
    ++ (encodeUIntLE 8 message.orderIdOptional
    ++ (encodeUIntLE 8 message.instrumentId
    ++ (encodeUInt 1 message.reasonCancelOrderRejectReason
    ++ (Details.encode message.details)))))))

def decode (bytes : List UInt8) : Option (CancelOrderRejectMessage × List UInt8) := do
  let (timestamp, bytes) ← decodeUIntLE 8 bytes
  let (execId, bytes) ← decodeUIntLE 8 bytes
  let (clientOrderId, bytes) ← decodeUIntLE 8 bytes
  let (correlationId, bytes) ← decodeUIntLE 8 bytes
  let (orderIdOptional, bytes) ← decodeUIntLE 8 bytes
  let (instrumentId, bytes) ← decodeUIntLE 8 bytes
  let (reasonCancelOrderRejectReason, bytes) ← decodeUInt 1 bytes
  let (details, bytes) ← Details.decode bytes
  pure ({ timestamp, execId, clientOrderId, correlationId, orderIdOptional, instrumentId, reasonCancelOrderRejectReason, details }, bytes)

theorem encode_length_pos (message : CancelOrderRejectMessage) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUIntLE_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : CancelOrderRejectMessage) : (encode message).length ≤ 305 := by
  have bound_details := Details.encode_length_le message.details
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, encodeUIntLE_length, encodeUInt_length]
  omega

@[simp] theorem decode_encode (message : CancelOrderRejectMessage) (rest : List UInt8) :
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
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [Details.decode_encode, some_bind]
  rfl

end CancelOrderRejectMessage

/-- Bid Filled Qty: 9 bytes -/
structure BidFilledQty where
  mantissa : BitVec 64
  exponent : BitVec 8
  deriving DecidableEq, Repr

namespace BidFilledQty

def encode (message : BidFilledQty) : List UInt8 :=
  encodeUIntLE 8 message.mantissa
    ++ (encodeUInt 1 message.exponent)

def decode (bytes : List UInt8) : Option (BidFilledQty × List UInt8) := do
  let (mantissa, bytes) ← decodeUIntLE 8 bytes
  let (exponent, bytes) ← decodeUInt 1 bytes
  pure ({ mantissa, exponent }, bytes)

@[simp] theorem encode_length (message : BidFilledQty) : (encode message).length = 9 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, encodeUInt_length]

theorem encode_length_pos (message : BidFilledQty) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : BidFilledQty) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end BidFilledQty

/-- Ask Filled Qty: 9 bytes -/
structure AskFilledQty where
  mantissa : BitVec 64
  exponent : BitVec 8
  deriving DecidableEq, Repr

namespace AskFilledQty

def encode (message : AskFilledQty) : List UInt8 :=
  encodeUIntLE 8 message.mantissa
    ++ (encodeUInt 1 message.exponent)

def decode (bytes : List UInt8) : Option (AskFilledQty × List UInt8) := do
  let (mantissa, bytes) ← decodeUIntLE 8 bytes
  let (exponent, bytes) ← decodeUInt 1 bytes
  pure ({ mantissa, exponent }, bytes)

@[simp] theorem encode_length (message : AskFilledQty) : (encode message).length = 9 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, encodeUInt_length]

theorem encode_length_pos (message : AskFilledQty) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : AskFilledQty) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end AskFilledQty

/-- Mass Quote Response Message quotes Group: 80 bytes -/
structure MassQuoteResponseMessageQuotesGroup where
  instrumentId : BitVec 64
  bidOrderId : BitVec 64
  askOrderId : BitVec 64
  bidPrice : BitVec 64
  askPrice : BitVec 64
  bidQty : BidQty
  askQty : AskQty
  bidFilledQty : BidFilledQty
  askFilledQty : AskFilledQty
  bidStatus : BitVec 8
  askStatus : BitVec 8
  bidRejectReason : BitVec 8
  askRejectReason : BitVec 8
  deriving DecidableEq, Repr

namespace MassQuoteResponseMessageQuotesGroup

def encode (message : MassQuoteResponseMessageQuotesGroup) : List UInt8 :=
  encodeUIntLE 8 message.instrumentId
    ++ (encodeUIntLE 8 message.bidOrderId
    ++ (encodeUIntLE 8 message.askOrderId
    ++ (encodeUIntLE 8 message.bidPrice
    ++ (encodeUIntLE 8 message.askPrice
    ++ (BidQty.encode message.bidQty
    ++ (AskQty.encode message.askQty
    ++ (BidFilledQty.encode message.bidFilledQty
    ++ (AskFilledQty.encode message.askFilledQty
    ++ (encodeUInt 1 message.bidStatus
    ++ (encodeUInt 1 message.askStatus
    ++ (encodeUInt 1 message.bidRejectReason
    ++ (encodeUInt 1 message.askRejectReason))))))))))))

def decode (bytes : List UInt8) : Option (MassQuoteResponseMessageQuotesGroup × List UInt8) := do
  let (instrumentId, bytes) ← decodeUIntLE 8 bytes
  let (bidOrderId, bytes) ← decodeUIntLE 8 bytes
  let (askOrderId, bytes) ← decodeUIntLE 8 bytes
  let (bidPrice, bytes) ← decodeUIntLE 8 bytes
  let (askPrice, bytes) ← decodeUIntLE 8 bytes
  let (bidQty, bytes) ← BidQty.decode bytes
  let (askQty, bytes) ← AskQty.decode bytes
  let (bidFilledQty, bytes) ← BidFilledQty.decode bytes
  let (askFilledQty, bytes) ← AskFilledQty.decode bytes
  let (bidStatus, bytes) ← decodeUInt 1 bytes
  let (askStatus, bytes) ← decodeUInt 1 bytes
  let (bidRejectReason, bytes) ← decodeUInt 1 bytes
  let (askRejectReason, bytes) ← decodeUInt 1 bytes
  pure ({ instrumentId, bidOrderId, askOrderId, bidPrice, askPrice, bidQty, askQty, bidFilledQty, askFilledQty, bidStatus, askStatus, bidRejectReason, askRejectReason }, bytes)

@[simp] theorem encode_length (message : MassQuoteResponseMessageQuotesGroup) : (encode message).length = 80 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, BidQty.encode_length, AskQty.encode_length, BidFilledQty.encode_length, AskFilledQty.encode_length, encodeUInt_length]

theorem encode_length_pos (message : MassQuoteResponseMessageQuotesGroup) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : MassQuoteResponseMessageQuotesGroup) (rest : List UInt8) :
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
  rw [List.append_assoc, BidQty.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, AskQty.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, BidFilledQty.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, AskFilledQty.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end MassQuoteResponseMessageQuotesGroup

/-- Mass Quote Response Message quotes Groups -/
structure MassQuoteResponseMessageQuotesGroups where
  blockLength : BitVec 16
  massQuoteResponseMessageQuotesGroup : Bounded 2 MassQuoteResponseMessageQuotesGroup
  deriving DecidableEq, Repr

namespace MassQuoteResponseMessageQuotesGroups

def encode (message : MassQuoteResponseMessageQuotesGroups) : List UInt8 :=
  encodeUIntLE 2 message.blockLength
    ++ (encodeUIntLE 2 (BitVec.ofNat (8 * 2) message.massQuoteResponseMessageQuotesGroup.val.length)
    ++ (encodeMany MassQuoteResponseMessageQuotesGroup.encode message.massQuoteResponseMessageQuotesGroup.val))

def decode (bytes : List UInt8) : Option (MassQuoteResponseMessageQuotesGroups × List UInt8) := do
  let (blockLength, bytes) ← decodeUIntLE 2 bytes
  let (numInGroup, bytes) ← decodeUIntLE 2 bytes
  let (massQuoteResponseMessageQuotesGroup_, bytes) ← decodeMany MassQuoteResponseMessageQuotesGroup.decode numInGroup.toNat bytes
  if fits_massQuoteResponseMessageQuotesGroup : massQuoteResponseMessageQuotesGroup_.length < 256 ^ 2 then
    pure ({ blockLength, massQuoteResponseMessageQuotesGroup := ⟨massQuoteResponseMessageQuotesGroup_, fits_massQuoteResponseMessageQuotesGroup⟩ }, bytes)
  else none

theorem encode_length_pos (message : MassQuoteResponseMessageQuotesGroups) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUIntLE_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : MassQuoteResponseMessageQuotesGroups) : (encode message).length ≤ 5242804 := by
  have bound_massQuoteResponseMessageQuotesGroup := message.massQuoteResponseMessageQuotesGroup.length_lt
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, encodeUIntLE_length, encodeMany_length_const MassQuoteResponseMessageQuotesGroup.encode 80 MassQuoteResponseMessageQuotesGroup.encode_length]
  omega

@[simp] theorem decode_encode (message : MassQuoteResponseMessageQuotesGroups) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeMany_bounded 2 MassQuoteResponseMessageQuotesGroup.encode MassQuoteResponseMessageQuotesGroup.decode MassQuoteResponseMessageQuotesGroup.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.massQuoteResponseMessageQuotesGroup.length_lt]
  rfl

end MassQuoteResponseMessageQuotesGroups

/-- Mass Quote Response Message bid Fills Group: 33 bytes -/
structure MassQuoteResponseMessageBidFillsGroup where
  matchId : BitVec 64
  instrumentId : BitVec 64
  fillPrice : BitVec 64
  fillQty : FillQty
  deriving DecidableEq, Repr

namespace MassQuoteResponseMessageBidFillsGroup

def encode (message : MassQuoteResponseMessageBidFillsGroup) : List UInt8 :=
  encodeUIntLE 8 message.matchId
    ++ (encodeUIntLE 8 message.instrumentId
    ++ (encodeUIntLE 8 message.fillPrice
    ++ (FillQty.encode message.fillQty)))

def decode (bytes : List UInt8) : Option (MassQuoteResponseMessageBidFillsGroup × List UInt8) := do
  let (matchId, bytes) ← decodeUIntLE 8 bytes
  let (instrumentId, bytes) ← decodeUIntLE 8 bytes
  let (fillPrice, bytes) ← decodeUIntLE 8 bytes
  let (fillQty, bytes) ← FillQty.decode bytes
  pure ({ matchId, instrumentId, fillPrice, fillQty }, bytes)

@[simp] theorem encode_length (message : MassQuoteResponseMessageBidFillsGroup) : (encode message).length = 33 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, FillQty.encode_length]

theorem encode_length_pos (message : MassQuoteResponseMessageBidFillsGroup) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : MassQuoteResponseMessageBidFillsGroup) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [FillQty.decode_encode, some_bind]
  rfl

end MassQuoteResponseMessageBidFillsGroup

/-- Mass Quote Response Message bid Fills Groups -/
structure MassQuoteResponseMessageBidFillsGroups where
  blockLength : BitVec 16
  massQuoteResponseMessageBidFillsGroup : Bounded 2 MassQuoteResponseMessageBidFillsGroup
  deriving DecidableEq, Repr

namespace MassQuoteResponseMessageBidFillsGroups

def encode (message : MassQuoteResponseMessageBidFillsGroups) : List UInt8 :=
  encodeUIntLE 2 message.blockLength
    ++ (encodeUIntLE 2 (BitVec.ofNat (8 * 2) message.massQuoteResponseMessageBidFillsGroup.val.length)
    ++ (encodeMany MassQuoteResponseMessageBidFillsGroup.encode message.massQuoteResponseMessageBidFillsGroup.val))

def decode (bytes : List UInt8) : Option (MassQuoteResponseMessageBidFillsGroups × List UInt8) := do
  let (blockLength, bytes) ← decodeUIntLE 2 bytes
  let (numInGroup, bytes) ← decodeUIntLE 2 bytes
  let (massQuoteResponseMessageBidFillsGroup_, bytes) ← decodeMany MassQuoteResponseMessageBidFillsGroup.decode numInGroup.toNat bytes
  if fits_massQuoteResponseMessageBidFillsGroup : massQuoteResponseMessageBidFillsGroup_.length < 256 ^ 2 then
    pure ({ blockLength, massQuoteResponseMessageBidFillsGroup := ⟨massQuoteResponseMessageBidFillsGroup_, fits_massQuoteResponseMessageBidFillsGroup⟩ }, bytes)
  else none

theorem encode_length_pos (message : MassQuoteResponseMessageBidFillsGroups) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUIntLE_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : MassQuoteResponseMessageBidFillsGroups) : (encode message).length ≤ 2162659 := by
  have bound_massQuoteResponseMessageBidFillsGroup := message.massQuoteResponseMessageBidFillsGroup.length_lt
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, encodeUIntLE_length, encodeMany_length_const MassQuoteResponseMessageBidFillsGroup.encode 33 MassQuoteResponseMessageBidFillsGroup.encode_length]
  omega

@[simp] theorem decode_encode (message : MassQuoteResponseMessageBidFillsGroups) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeMany_bounded 2 MassQuoteResponseMessageBidFillsGroup.encode MassQuoteResponseMessageBidFillsGroup.decode MassQuoteResponseMessageBidFillsGroup.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.massQuoteResponseMessageBidFillsGroup.length_lt]
  rfl

end MassQuoteResponseMessageBidFillsGroups

/-- Mass Quote Response Message ask Fills Group: 33 bytes -/
structure MassQuoteResponseMessageAskFillsGroup where
  matchId : BitVec 64
  instrumentId : BitVec 64
  fillPrice : BitVec 64
  fillQty : FillQty
  deriving DecidableEq, Repr

namespace MassQuoteResponseMessageAskFillsGroup

def encode (message : MassQuoteResponseMessageAskFillsGroup) : List UInt8 :=
  encodeUIntLE 8 message.matchId
    ++ (encodeUIntLE 8 message.instrumentId
    ++ (encodeUIntLE 8 message.fillPrice
    ++ (FillQty.encode message.fillQty)))

def decode (bytes : List UInt8) : Option (MassQuoteResponseMessageAskFillsGroup × List UInt8) := do
  let (matchId, bytes) ← decodeUIntLE 8 bytes
  let (instrumentId, bytes) ← decodeUIntLE 8 bytes
  let (fillPrice, bytes) ← decodeUIntLE 8 bytes
  let (fillQty, bytes) ← FillQty.decode bytes
  pure ({ matchId, instrumentId, fillPrice, fillQty }, bytes)

@[simp] theorem encode_length (message : MassQuoteResponseMessageAskFillsGroup) : (encode message).length = 33 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, FillQty.encode_length]

theorem encode_length_pos (message : MassQuoteResponseMessageAskFillsGroup) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : MassQuoteResponseMessageAskFillsGroup) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [FillQty.decode_encode, some_bind]
  rfl

end MassQuoteResponseMessageAskFillsGroup

/-- Mass Quote Response Message ask Fills Groups -/
structure MassQuoteResponseMessageAskFillsGroups where
  blockLength : BitVec 16
  massQuoteResponseMessageAskFillsGroup : Bounded 2 MassQuoteResponseMessageAskFillsGroup
  deriving DecidableEq, Repr

namespace MassQuoteResponseMessageAskFillsGroups

def encode (message : MassQuoteResponseMessageAskFillsGroups) : List UInt8 :=
  encodeUIntLE 2 message.blockLength
    ++ (encodeUIntLE 2 (BitVec.ofNat (8 * 2) message.massQuoteResponseMessageAskFillsGroup.val.length)
    ++ (encodeMany MassQuoteResponseMessageAskFillsGroup.encode message.massQuoteResponseMessageAskFillsGroup.val))

def decode (bytes : List UInt8) : Option (MassQuoteResponseMessageAskFillsGroups × List UInt8) := do
  let (blockLength, bytes) ← decodeUIntLE 2 bytes
  let (numInGroup, bytes) ← decodeUIntLE 2 bytes
  let (massQuoteResponseMessageAskFillsGroup_, bytes) ← decodeMany MassQuoteResponseMessageAskFillsGroup.decode numInGroup.toNat bytes
  if fits_massQuoteResponseMessageAskFillsGroup : massQuoteResponseMessageAskFillsGroup_.length < 256 ^ 2 then
    pure ({ blockLength, massQuoteResponseMessageAskFillsGroup := ⟨massQuoteResponseMessageAskFillsGroup_, fits_massQuoteResponseMessageAskFillsGroup⟩ }, bytes)
  else none

theorem encode_length_pos (message : MassQuoteResponseMessageAskFillsGroups) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUIntLE_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : MassQuoteResponseMessageAskFillsGroups) : (encode message).length ≤ 2162659 := by
  have bound_massQuoteResponseMessageAskFillsGroup := message.massQuoteResponseMessageAskFillsGroup.length_lt
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, encodeUIntLE_length, encodeMany_length_const MassQuoteResponseMessageAskFillsGroup.encode 33 MassQuoteResponseMessageAskFillsGroup.encode_length]
  omega

@[simp] theorem decode_encode (message : MassQuoteResponseMessageAskFillsGroups) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeMany_bounded 2 MassQuoteResponseMessageAskFillsGroup.encode MassQuoteResponseMessageAskFillsGroup.decode MassQuoteResponseMessageAskFillsGroup.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.massQuoteResponseMessageAskFillsGroup.length_lt]
  rfl

end MassQuoteResponseMessageAskFillsGroups

/-- Mass Quote Response Message legs Group: 34 bytes -/
structure MassQuoteResponseMessageLegsGroup where
  matchId : BitVec 64
  fillId : BitVec 64
  fillPrice : BitVec 64
  fillQty : FillQty
  legSide : BitVec 8
  deriving DecidableEq, Repr

namespace MassQuoteResponseMessageLegsGroup

def encode (message : MassQuoteResponseMessageLegsGroup) : List UInt8 :=
  encodeUIntLE 8 message.matchId
    ++ (encodeUIntLE 8 message.fillId
    ++ (encodeUIntLE 8 message.fillPrice
    ++ (FillQty.encode message.fillQty
    ++ (encodeUInt 1 message.legSide))))

def decode (bytes : List UInt8) : Option (MassQuoteResponseMessageLegsGroup × List UInt8) := do
  let (matchId, bytes) ← decodeUIntLE 8 bytes
  let (fillId, bytes) ← decodeUIntLE 8 bytes
  let (fillPrice, bytes) ← decodeUIntLE 8 bytes
  let (fillQty, bytes) ← FillQty.decode bytes
  let (legSide, bytes) ← decodeUInt 1 bytes
  pure ({ matchId, fillId, fillPrice, fillQty, legSide }, bytes)

@[simp] theorem encode_length (message : MassQuoteResponseMessageLegsGroup) : (encode message).length = 34 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, FillQty.encode_length, encodeUInt_length]

theorem encode_length_pos (message : MassQuoteResponseMessageLegsGroup) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : MassQuoteResponseMessageLegsGroup) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, FillQty.decode_encode, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end MassQuoteResponseMessageLegsGroup

/-- Mass Quote Response Message legs Groups -/
structure MassQuoteResponseMessageLegsGroups where
  blockLength : BitVec 16
  massQuoteResponseMessageLegsGroup : Bounded 2 MassQuoteResponseMessageLegsGroup
  deriving DecidableEq, Repr

namespace MassQuoteResponseMessageLegsGroups

def encode (message : MassQuoteResponseMessageLegsGroups) : List UInt8 :=
  encodeUIntLE 2 message.blockLength
    ++ (encodeUIntLE 2 (BitVec.ofNat (8 * 2) message.massQuoteResponseMessageLegsGroup.val.length)
    ++ (encodeMany MassQuoteResponseMessageLegsGroup.encode message.massQuoteResponseMessageLegsGroup.val))

def decode (bytes : List UInt8) : Option (MassQuoteResponseMessageLegsGroups × List UInt8) := do
  let (blockLength, bytes) ← decodeUIntLE 2 bytes
  let (numInGroup, bytes) ← decodeUIntLE 2 bytes
  let (massQuoteResponseMessageLegsGroup_, bytes) ← decodeMany MassQuoteResponseMessageLegsGroup.decode numInGroup.toNat bytes
  if fits_massQuoteResponseMessageLegsGroup : massQuoteResponseMessageLegsGroup_.length < 256 ^ 2 then
    pure ({ blockLength, massQuoteResponseMessageLegsGroup := ⟨massQuoteResponseMessageLegsGroup_, fits_massQuoteResponseMessageLegsGroup⟩ }, bytes)
  else none

theorem encode_length_pos (message : MassQuoteResponseMessageLegsGroups) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUIntLE_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : MassQuoteResponseMessageLegsGroups) : (encode message).length ≤ 2228194 := by
  have bound_massQuoteResponseMessageLegsGroup := message.massQuoteResponseMessageLegsGroup.length_lt
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, encodeUIntLE_length, encodeMany_length_const MassQuoteResponseMessageLegsGroup.encode 34 MassQuoteResponseMessageLegsGroup.encode_length]
  omega

@[simp] theorem decode_encode (message : MassQuoteResponseMessageLegsGroups) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeMany_bounded 2 MassQuoteResponseMessageLegsGroup.encode MassQuoteResponseMessageLegsGroup.decode MassQuoteResponseMessageLegsGroup.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.massQuoteResponseMessageLegsGroup.length_lt]
  rfl

end MassQuoteResponseMessageLegsGroups

/-- Mass Quote Response Message -/
structure MassQuoteResponseMessage where
  timestamp : BitVec 64
  execId : BitVec 64
  quoteId : BitVec 64
  correlationId : BitVec 64
  mmpGroupId : BitVec 64
  receiveTime : BitVec 64
  massQuoteResponseMessageQuotesGroups : MassQuoteResponseMessageQuotesGroups
  massQuoteResponseMessageBidFillsGroups : MassQuoteResponseMessageBidFillsGroups
  massQuoteResponseMessageAskFillsGroups : MassQuoteResponseMessageAskFillsGroups
  massQuoteResponseMessageLegsGroups : MassQuoteResponseMessageLegsGroups
  deriving DecidableEq, Repr

namespace MassQuoteResponseMessage

def encode (message : MassQuoteResponseMessage) : List UInt8 :=
  encodeUIntLE 8 message.timestamp
    ++ (encodeUIntLE 8 message.execId
    ++ (encodeUIntLE 8 message.quoteId
    ++ (encodeUIntLE 8 message.correlationId
    ++ (encodeUIntLE 8 message.mmpGroupId
    ++ (encodeUIntLE 8 message.receiveTime
    ++ (MassQuoteResponseMessageQuotesGroups.encode message.massQuoteResponseMessageQuotesGroups
    ++ (MassQuoteResponseMessageBidFillsGroups.encode message.massQuoteResponseMessageBidFillsGroups
    ++ (MassQuoteResponseMessageAskFillsGroups.encode message.massQuoteResponseMessageAskFillsGroups
    ++ (MassQuoteResponseMessageLegsGroups.encode message.massQuoteResponseMessageLegsGroups)))))))))

def decode (bytes : List UInt8) : Option (MassQuoteResponseMessage × List UInt8) := do
  let (timestamp, bytes) ← decodeUIntLE 8 bytes
  let (execId, bytes) ← decodeUIntLE 8 bytes
  let (quoteId, bytes) ← decodeUIntLE 8 bytes
  let (correlationId, bytes) ← decodeUIntLE 8 bytes
  let (mmpGroupId, bytes) ← decodeUIntLE 8 bytes
  let (receiveTime, bytes) ← decodeUIntLE 8 bytes
  let (massQuoteResponseMessageQuotesGroups, bytes) ← MassQuoteResponseMessageQuotesGroups.decode bytes
  let (massQuoteResponseMessageBidFillsGroups, bytes) ← MassQuoteResponseMessageBidFillsGroups.decode bytes
  let (massQuoteResponseMessageAskFillsGroups, bytes) ← MassQuoteResponseMessageAskFillsGroups.decode bytes
  let (massQuoteResponseMessageLegsGroups, bytes) ← MassQuoteResponseMessageLegsGroups.decode bytes
  pure ({ timestamp, execId, quoteId, correlationId, mmpGroupId, receiveTime, massQuoteResponseMessageQuotesGroups, massQuoteResponseMessageBidFillsGroups, massQuoteResponseMessageAskFillsGroups, massQuoteResponseMessageLegsGroups }, bytes)

theorem encode_length_pos (message : MassQuoteResponseMessage) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUIntLE_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : MassQuoteResponseMessage) : (encode message).length ≤ 11796364 := by
  have bound_massQuoteResponseMessageQuotesGroups := MassQuoteResponseMessageQuotesGroups.encode_length_le message.massQuoteResponseMessageQuotesGroups
  have bound_massQuoteResponseMessageBidFillsGroups := MassQuoteResponseMessageBidFillsGroups.encode_length_le message.massQuoteResponseMessageBidFillsGroups
  have bound_massQuoteResponseMessageAskFillsGroups := MassQuoteResponseMessageAskFillsGroups.encode_length_le message.massQuoteResponseMessageAskFillsGroups
  have bound_massQuoteResponseMessageLegsGroups := MassQuoteResponseMessageLegsGroups.encode_length_le message.massQuoteResponseMessageLegsGroups
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, encodeUIntLE_length]
  omega

@[simp] theorem decode_encode (message : MassQuoteResponseMessage) (rest : List UInt8) :
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
  rw [List.append_assoc, MassQuoteResponseMessageQuotesGroups.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, MassQuoteResponseMessageBidFillsGroups.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, MassQuoteResponseMessageAskFillsGroups.decode_encode, some_bind]
  dsimp only
  rw [MassQuoteResponseMessageLegsGroups.decode_encode, some_bind]
  rfl

end MassQuoteResponseMessage

/-- Mass Quote Reject Message -/
structure MassQuoteRejectMessage where
  timestamp : BitVec 64
  execId : BitVec 64
  quoteId : BitVec 64
  correlationId : BitVec 64
  mmpGroupId : BitVec 64
  reasonMassQuoteRejectReason : BitVec 8
  details : Details
  deriving DecidableEq, Repr

namespace MassQuoteRejectMessage

def encode (message : MassQuoteRejectMessage) : List UInt8 :=
  encodeUIntLE 8 message.timestamp
    ++ (encodeUIntLE 8 message.execId
    ++ (encodeUIntLE 8 message.quoteId
    ++ (encodeUIntLE 8 message.correlationId
    ++ (encodeUIntLE 8 message.mmpGroupId
    ++ (encodeUInt 1 message.reasonMassQuoteRejectReason
    ++ (Details.encode message.details))))))

def decode (bytes : List UInt8) : Option (MassQuoteRejectMessage × List UInt8) := do
  let (timestamp, bytes) ← decodeUIntLE 8 bytes
  let (execId, bytes) ← decodeUIntLE 8 bytes
  let (quoteId, bytes) ← decodeUIntLE 8 bytes
  let (correlationId, bytes) ← decodeUIntLE 8 bytes
  let (mmpGroupId, bytes) ← decodeUIntLE 8 bytes
  let (reasonMassQuoteRejectReason, bytes) ← decodeUInt 1 bytes
  let (details, bytes) ← Details.decode bytes
  pure ({ timestamp, execId, quoteId, correlationId, mmpGroupId, reasonMassQuoteRejectReason, details }, bytes)

theorem encode_length_pos (message : MassQuoteRejectMessage) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUIntLE_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : MassQuoteRejectMessage) : (encode message).length ≤ 297 := by
  have bound_details := Details.encode_length_le message.details
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, encodeUIntLE_length, encodeUInt_length]
  omega

@[simp] theorem decode_encode (message : MassQuoteRejectMessage) (rest : List UInt8) :
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
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [Details.decode_encode, some_bind]
  rfl

end MassQuoteRejectMessage

/-- Mass Cancel Response Message: 36 bytes -/
structure MassCancelResponseMessage where
  timestamp : BitVec 64
  execId : BitVec 64
  correlationId : BitVec 64
  receiveTime : BitVec 64
  totalOrderCount : BitVec 32
  deriving DecidableEq, Repr

namespace MassCancelResponseMessage

def encode (message : MassCancelResponseMessage) : List UInt8 :=
  encodeUIntLE 8 message.timestamp
    ++ (encodeUIntLE 8 message.execId
    ++ (encodeUIntLE 8 message.correlationId
    ++ (encodeUIntLE 8 message.receiveTime
    ++ (encodeUIntLE 4 message.totalOrderCount))))

def decode (bytes : List UInt8) : Option (MassCancelResponseMessage × List UInt8) := do
  let (timestamp, bytes) ← decodeUIntLE 8 bytes
  let (execId, bytes) ← decodeUIntLE 8 bytes
  let (correlationId, bytes) ← decodeUIntLE 8 bytes
  let (receiveTime, bytes) ← decodeUIntLE 8 bytes
  let (totalOrderCount, bytes) ← decodeUIntLE 4 bytes
  pure ({ timestamp, execId, correlationId, receiveTime, totalOrderCount }, bytes)

@[simp] theorem encode_length (message : MassCancelResponseMessage) : (encode message).length = 36 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length]

theorem encode_length_pos (message : MassCancelResponseMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : MassCancelResponseMessage) (rest : List UInt8) :
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

end MassCancelResponseMessage

/-- Mass Cancel Reject Message -/
structure MassCancelRejectMessage where
  timestamp : BitVec 64
  execId : BitVec 64
  correlationId : BitVec 64
  reasonMassCancelRejectReason : BitVec 8
  details : Details
  deriving DecidableEq, Repr

namespace MassCancelRejectMessage

def encode (message : MassCancelRejectMessage) : List UInt8 :=
  encodeUIntLE 8 message.timestamp
    ++ (encodeUIntLE 8 message.execId
    ++ (encodeUIntLE 8 message.correlationId
    ++ (encodeUInt 1 message.reasonMassCancelRejectReason
    ++ (Details.encode message.details))))

def decode (bytes : List UInt8) : Option (MassCancelRejectMessage × List UInt8) := do
  let (timestamp, bytes) ← decodeUIntLE 8 bytes
  let (execId, bytes) ← decodeUIntLE 8 bytes
  let (correlationId, bytes) ← decodeUIntLE 8 bytes
  let (reasonMassCancelRejectReason, bytes) ← decodeUInt 1 bytes
  let (details, bytes) ← Details.decode bytes
  pure ({ timestamp, execId, correlationId, reasonMassCancelRejectReason, details }, bytes)

theorem encode_length_pos (message : MassCancelRejectMessage) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUIntLE_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : MassCancelRejectMessage) : (encode message).length ≤ 281 := by
  have bound_details := Details.encode_length_le message.details
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, encodeUIntLE_length, encodeUInt_length]
  omega

@[simp] theorem decode_encode (message : MassCancelRejectMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [Details.decode_encode, some_bind]
  rfl

end MassCancelRejectMessage

/-- Order Filled Message fills Group: 60 bytes -/
structure OrderFilledMessageFillsGroup where
  clientOrderId : BitVec 64
  orderId : BitVec 64
  instrumentId : BitVec 64
  matchId : BitVec 64
  price : BitVec 64
  fillQty : FillQty
  totalFilled : TotalFilled
  side : BitVec 8
  flagsFillFlags : BitVec 8
  deriving DecidableEq, Repr

namespace OrderFilledMessageFillsGroup

def encode (message : OrderFilledMessageFillsGroup) : List UInt8 :=
  encodeUIntLE 8 message.clientOrderId
    ++ (encodeUIntLE 8 message.orderId
    ++ (encodeUIntLE 8 message.instrumentId
    ++ (encodeUIntLE 8 message.matchId
    ++ (encodeUIntLE 8 message.price
    ++ (FillQty.encode message.fillQty
    ++ (TotalFilled.encode message.totalFilled
    ++ (encodeUInt 1 message.side
    ++ (encodeUIntLE 1 message.flagsFillFlags))))))))

def decode (bytes : List UInt8) : Option (OrderFilledMessageFillsGroup × List UInt8) := do
  let (clientOrderId, bytes) ← decodeUIntLE 8 bytes
  let (orderId, bytes) ← decodeUIntLE 8 bytes
  let (instrumentId, bytes) ← decodeUIntLE 8 bytes
  let (matchId, bytes) ← decodeUIntLE 8 bytes
  let (price, bytes) ← decodeUIntLE 8 bytes
  let (fillQty, bytes) ← FillQty.decode bytes
  let (totalFilled, bytes) ← TotalFilled.decode bytes
  let (side, bytes) ← decodeUInt 1 bytes
  let (flagsFillFlags, bytes) ← decodeUIntLE 1 bytes
  pure ({ clientOrderId, orderId, instrumentId, matchId, price, fillQty, totalFilled, side, flagsFillFlags }, bytes)

@[simp] theorem encode_length (message : OrderFilledMessageFillsGroup) : (encode message).length = 60 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, FillQty.encode_length, TotalFilled.encode_length, encodeUInt_length]

theorem encode_length_pos (message : OrderFilledMessageFillsGroup) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OrderFilledMessageFillsGroup) (rest : List UInt8) :
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
  rw [List.append_assoc, FillQty.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, TotalFilled.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end OrderFilledMessageFillsGroup

/-- Order Filled Message fills Groups -/
structure OrderFilledMessageFillsGroups where
  blockLength : BitVec 16
  orderFilledMessageFillsGroup : Bounded 2 OrderFilledMessageFillsGroup
  deriving DecidableEq, Repr

namespace OrderFilledMessageFillsGroups

def encode (message : OrderFilledMessageFillsGroups) : List UInt8 :=
  encodeUIntLE 2 message.blockLength
    ++ (encodeUIntLE 2 (BitVec.ofNat (8 * 2) message.orderFilledMessageFillsGroup.val.length)
    ++ (encodeMany OrderFilledMessageFillsGroup.encode message.orderFilledMessageFillsGroup.val))

def decode (bytes : List UInt8) : Option (OrderFilledMessageFillsGroups × List UInt8) := do
  let (blockLength, bytes) ← decodeUIntLE 2 bytes
  let (numInGroup, bytes) ← decodeUIntLE 2 bytes
  let (orderFilledMessageFillsGroup_, bytes) ← decodeMany OrderFilledMessageFillsGroup.decode numInGroup.toNat bytes
  if fits_orderFilledMessageFillsGroup : orderFilledMessageFillsGroup_.length < 256 ^ 2 then
    pure ({ blockLength, orderFilledMessageFillsGroup := ⟨orderFilledMessageFillsGroup_, fits_orderFilledMessageFillsGroup⟩ }, bytes)
  else none

theorem encode_length_pos (message : OrderFilledMessageFillsGroups) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUIntLE_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : OrderFilledMessageFillsGroups) : (encode message).length ≤ 3932104 := by
  have bound_orderFilledMessageFillsGroup := message.orderFilledMessageFillsGroup.length_lt
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, encodeUIntLE_length, encodeMany_length_const OrderFilledMessageFillsGroup.encode 60 OrderFilledMessageFillsGroup.encode_length]
  omega

@[simp] theorem decode_encode (message : OrderFilledMessageFillsGroups) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeMany_bounded 2 OrderFilledMessageFillsGroup.encode OrderFilledMessageFillsGroup.decode OrderFilledMessageFillsGroup.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.orderFilledMessageFillsGroup.length_lt]
  rfl

end OrderFilledMessageFillsGroups

/-- Order Filled Message legs Group: 34 bytes -/
structure OrderFilledMessageLegsGroup where
  matchId : BitVec 64
  fillId : BitVec 64
  price : BitVec 64
  fillQty : FillQty
  legSide : BitVec 8
  deriving DecidableEq, Repr

namespace OrderFilledMessageLegsGroup

def encode (message : OrderFilledMessageLegsGroup) : List UInt8 :=
  encodeUIntLE 8 message.matchId
    ++ (encodeUIntLE 8 message.fillId
    ++ (encodeUIntLE 8 message.price
    ++ (FillQty.encode message.fillQty
    ++ (encodeUInt 1 message.legSide))))

def decode (bytes : List UInt8) : Option (OrderFilledMessageLegsGroup × List UInt8) := do
  let (matchId, bytes) ← decodeUIntLE 8 bytes
  let (fillId, bytes) ← decodeUIntLE 8 bytes
  let (price, bytes) ← decodeUIntLE 8 bytes
  let (fillQty, bytes) ← FillQty.decode bytes
  let (legSide, bytes) ← decodeUInt 1 bytes
  pure ({ matchId, fillId, price, fillQty, legSide }, bytes)

@[simp] theorem encode_length (message : OrderFilledMessageLegsGroup) : (encode message).length = 34 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, FillQty.encode_length, encodeUInt_length]

theorem encode_length_pos (message : OrderFilledMessageLegsGroup) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OrderFilledMessageLegsGroup) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, FillQty.decode_encode, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end OrderFilledMessageLegsGroup

/-- Order Filled Message legs Groups -/
structure OrderFilledMessageLegsGroups where
  blockLength : BitVec 16
  orderFilledMessageLegsGroup : Bounded 2 OrderFilledMessageLegsGroup
  deriving DecidableEq, Repr

namespace OrderFilledMessageLegsGroups

def encode (message : OrderFilledMessageLegsGroups) : List UInt8 :=
  encodeUIntLE 2 message.blockLength
    ++ (encodeUIntLE 2 (BitVec.ofNat (8 * 2) message.orderFilledMessageLegsGroup.val.length)
    ++ (encodeMany OrderFilledMessageLegsGroup.encode message.orderFilledMessageLegsGroup.val))

def decode (bytes : List UInt8) : Option (OrderFilledMessageLegsGroups × List UInt8) := do
  let (blockLength, bytes) ← decodeUIntLE 2 bytes
  let (numInGroup, bytes) ← decodeUIntLE 2 bytes
  let (orderFilledMessageLegsGroup_, bytes) ← decodeMany OrderFilledMessageLegsGroup.decode numInGroup.toNat bytes
  if fits_orderFilledMessageLegsGroup : orderFilledMessageLegsGroup_.length < 256 ^ 2 then
    pure ({ blockLength, orderFilledMessageLegsGroup := ⟨orderFilledMessageLegsGroup_, fits_orderFilledMessageLegsGroup⟩ }, bytes)
  else none

theorem encode_length_pos (message : OrderFilledMessageLegsGroups) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUIntLE_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : OrderFilledMessageLegsGroups) : (encode message).length ≤ 2228194 := by
  have bound_orderFilledMessageLegsGroup := message.orderFilledMessageLegsGroup.length_lt
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, encodeUIntLE_length, encodeMany_length_const OrderFilledMessageLegsGroup.encode 34 OrderFilledMessageLegsGroup.encode_length]
  omega

@[simp] theorem decode_encode (message : OrderFilledMessageLegsGroups) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeMany_bounded 2 OrderFilledMessageLegsGroup.encode OrderFilledMessageLegsGroup.decode OrderFilledMessageLegsGroup.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.orderFilledMessageLegsGroup.length_lt]
  rfl

end OrderFilledMessageLegsGroups

/-- Order Filled Message -/
structure OrderFilledMessage where
  timestamp : BitVec 64
  execId : BitVec 64
  orderFilledMessageFillsGroups : OrderFilledMessageFillsGroups
  orderFilledMessageLegsGroups : OrderFilledMessageLegsGroups
  deriving DecidableEq, Repr

namespace OrderFilledMessage

def encode (message : OrderFilledMessage) : List UInt8 :=
  encodeUIntLE 8 message.timestamp
    ++ (encodeUIntLE 8 message.execId
    ++ (OrderFilledMessageFillsGroups.encode message.orderFilledMessageFillsGroups
    ++ (OrderFilledMessageLegsGroups.encode message.orderFilledMessageLegsGroups)))

def decode (bytes : List UInt8) : Option (OrderFilledMessage × List UInt8) := do
  let (timestamp, bytes) ← decodeUIntLE 8 bytes
  let (execId, bytes) ← decodeUIntLE 8 bytes
  let (orderFilledMessageFillsGroups, bytes) ← OrderFilledMessageFillsGroups.decode bytes
  let (orderFilledMessageLegsGroups, bytes) ← OrderFilledMessageLegsGroups.decode bytes
  pure ({ timestamp, execId, orderFilledMessageFillsGroups, orderFilledMessageLegsGroups }, bytes)

theorem encode_length_pos (message : OrderFilledMessage) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUIntLE_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : OrderFilledMessage) : (encode message).length ≤ 6160314 := by
  have bound_orderFilledMessageFillsGroups := OrderFilledMessageFillsGroups.encode_length_le message.orderFilledMessageFillsGroups
  have bound_orderFilledMessageLegsGroups := OrderFilledMessageLegsGroups.encode_length_le message.orderFilledMessageLegsGroups
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, encodeUIntLE_length]
  omega

@[simp] theorem decode_encode (message : OrderFilledMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, OrderFilledMessageFillsGroups.decode_encode, some_bind]
  dsimp only
  rw [OrderFilledMessageLegsGroups.decode_encode, some_bind]
  rfl

end OrderFilledMessage

/-- Orders Canceled Message orders Group: 35 bytes -/
structure OrdersCanceledMessageOrdersGroup where
  clientOrderId : BitVec 64
  orderId : BitVec 64
  instrumentId : BitVec 64
  totalFilled : TotalFilled
  cancelReason : BitVec 8
  flagsCancelFlags : BitVec 8
  deriving DecidableEq, Repr

namespace OrdersCanceledMessageOrdersGroup

def encode (message : OrdersCanceledMessageOrdersGroup) : List UInt8 :=
  encodeUIntLE 8 message.clientOrderId
    ++ (encodeUIntLE 8 message.orderId
    ++ (encodeUIntLE 8 message.instrumentId
    ++ (TotalFilled.encode message.totalFilled
    ++ (encodeUInt 1 message.cancelReason
    ++ (encodeUIntLE 1 message.flagsCancelFlags)))))

def decode (bytes : List UInt8) : Option (OrdersCanceledMessageOrdersGroup × List UInt8) := do
  let (clientOrderId, bytes) ← decodeUIntLE 8 bytes
  let (orderId, bytes) ← decodeUIntLE 8 bytes
  let (instrumentId, bytes) ← decodeUIntLE 8 bytes
  let (totalFilled, bytes) ← TotalFilled.decode bytes
  let (cancelReason, bytes) ← decodeUInt 1 bytes
  let (flagsCancelFlags, bytes) ← decodeUIntLE 1 bytes
  pure ({ clientOrderId, orderId, instrumentId, totalFilled, cancelReason, flagsCancelFlags }, bytes)

@[simp] theorem encode_length (message : OrdersCanceledMessageOrdersGroup) : (encode message).length = 35 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, TotalFilled.encode_length, encodeUInt_length]

theorem encode_length_pos (message : OrdersCanceledMessageOrdersGroup) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OrdersCanceledMessageOrdersGroup) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, TotalFilled.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end OrdersCanceledMessageOrdersGroup

/-- Orders Canceled Message orders Groups -/
structure OrdersCanceledMessageOrdersGroups where
  blockLength : BitVec 16
  ordersCanceledMessageOrdersGroup : Bounded 2 OrdersCanceledMessageOrdersGroup
  deriving DecidableEq, Repr

namespace OrdersCanceledMessageOrdersGroups

def encode (message : OrdersCanceledMessageOrdersGroups) : List UInt8 :=
  encodeUIntLE 2 message.blockLength
    ++ (encodeUIntLE 2 (BitVec.ofNat (8 * 2) message.ordersCanceledMessageOrdersGroup.val.length)
    ++ (encodeMany OrdersCanceledMessageOrdersGroup.encode message.ordersCanceledMessageOrdersGroup.val))

def decode (bytes : List UInt8) : Option (OrdersCanceledMessageOrdersGroups × List UInt8) := do
  let (blockLength, bytes) ← decodeUIntLE 2 bytes
  let (numInGroup, bytes) ← decodeUIntLE 2 bytes
  let (ordersCanceledMessageOrdersGroup_, bytes) ← decodeMany OrdersCanceledMessageOrdersGroup.decode numInGroup.toNat bytes
  if fits_ordersCanceledMessageOrdersGroup : ordersCanceledMessageOrdersGroup_.length < 256 ^ 2 then
    pure ({ blockLength, ordersCanceledMessageOrdersGroup := ⟨ordersCanceledMessageOrdersGroup_, fits_ordersCanceledMessageOrdersGroup⟩ }, bytes)
  else none

theorem encode_length_pos (message : OrdersCanceledMessageOrdersGroups) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUIntLE_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : OrdersCanceledMessageOrdersGroups) : (encode message).length ≤ 2293729 := by
  have bound_ordersCanceledMessageOrdersGroup := message.ordersCanceledMessageOrdersGroup.length_lt
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, encodeUIntLE_length, encodeMany_length_const OrdersCanceledMessageOrdersGroup.encode 35 OrdersCanceledMessageOrdersGroup.encode_length]
  omega

@[simp] theorem decode_encode (message : OrdersCanceledMessageOrdersGroups) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeMany_bounded 2 OrdersCanceledMessageOrdersGroup.encode OrdersCanceledMessageOrdersGroup.decode OrdersCanceledMessageOrdersGroup.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.ordersCanceledMessageOrdersGroup.length_lt]
  rfl

end OrdersCanceledMessageOrdersGroups

/-- Orders Canceled Message -/
structure OrdersCanceledMessage where
  timestamp : BitVec 64
  execId : BitVec 64
  flagsMultiPartEventFlags : BitVec 8
  ordersCanceledMessageOrdersGroups : OrdersCanceledMessageOrdersGroups
  deriving DecidableEq, Repr

namespace OrdersCanceledMessage

def encode (message : OrdersCanceledMessage) : List UInt8 :=
  encodeUIntLE 8 message.timestamp
    ++ (encodeUIntLE 8 message.execId
    ++ (encodeUIntLE 1 message.flagsMultiPartEventFlags
    ++ (OrdersCanceledMessageOrdersGroups.encode message.ordersCanceledMessageOrdersGroups)))

def decode (bytes : List UInt8) : Option (OrdersCanceledMessage × List UInt8) := do
  let (timestamp, bytes) ← decodeUIntLE 8 bytes
  let (execId, bytes) ← decodeUIntLE 8 bytes
  let (flagsMultiPartEventFlags, bytes) ← decodeUIntLE 1 bytes
  let (ordersCanceledMessageOrdersGroups, bytes) ← OrdersCanceledMessageOrdersGroups.decode bytes
  pure ({ timestamp, execId, flagsMultiPartEventFlags, ordersCanceledMessageOrdersGroups }, bytes)

theorem encode_length_pos (message : OrdersCanceledMessage) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUIntLE_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : OrdersCanceledMessage) : (encode message).length ≤ 2293746 := by
  have bound_ordersCanceledMessageOrdersGroups := OrdersCanceledMessageOrdersGroups.encode_length_le message.ordersCanceledMessageOrdersGroups
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, encodeUIntLE_length]
  omega

@[simp] theorem decode_encode (message : OrdersCanceledMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [OrdersCanceledMessageOrdersGroups.decode_encode, some_bind]
  rfl

end OrdersCanceledMessage

/-- Order Placed Message fills Group: 25 bytes -/
structure OrderPlacedMessageFillsGroup where
  matchId : BitVec 64
  fillPrice : BitVec 64
  fillQty : FillQty
  deriving DecidableEq, Repr

namespace OrderPlacedMessageFillsGroup

def encode (message : OrderPlacedMessageFillsGroup) : List UInt8 :=
  encodeUIntLE 8 message.matchId
    ++ (encodeUIntLE 8 message.fillPrice
    ++ (FillQty.encode message.fillQty))

def decode (bytes : List UInt8) : Option (OrderPlacedMessageFillsGroup × List UInt8) := do
  let (matchId, bytes) ← decodeUIntLE 8 bytes
  let (fillPrice, bytes) ← decodeUIntLE 8 bytes
  let (fillQty, bytes) ← FillQty.decode bytes
  pure ({ matchId, fillPrice, fillQty }, bytes)

@[simp] theorem encode_length (message : OrderPlacedMessageFillsGroup) : (encode message).length = 25 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, FillQty.encode_length]

theorem encode_length_pos (message : OrderPlacedMessageFillsGroup) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OrderPlacedMessageFillsGroup) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [FillQty.decode_encode, some_bind]
  rfl

end OrderPlacedMessageFillsGroup

/-- Order Placed Message fills Groups -/
structure OrderPlacedMessageFillsGroups where
  blockLength : BitVec 16
  orderPlacedMessageFillsGroup : Bounded 2 OrderPlacedMessageFillsGroup
  deriving DecidableEq, Repr

namespace OrderPlacedMessageFillsGroups

def encode (message : OrderPlacedMessageFillsGroups) : List UInt8 :=
  encodeUIntLE 2 message.blockLength
    ++ (encodeUIntLE 2 (BitVec.ofNat (8 * 2) message.orderPlacedMessageFillsGroup.val.length)
    ++ (encodeMany OrderPlacedMessageFillsGroup.encode message.orderPlacedMessageFillsGroup.val))

def decode (bytes : List UInt8) : Option (OrderPlacedMessageFillsGroups × List UInt8) := do
  let (blockLength, bytes) ← decodeUIntLE 2 bytes
  let (numInGroup, bytes) ← decodeUIntLE 2 bytes
  let (orderPlacedMessageFillsGroup_, bytes) ← decodeMany OrderPlacedMessageFillsGroup.decode numInGroup.toNat bytes
  if fits_orderPlacedMessageFillsGroup : orderPlacedMessageFillsGroup_.length < 256 ^ 2 then
    pure ({ blockLength, orderPlacedMessageFillsGroup := ⟨orderPlacedMessageFillsGroup_, fits_orderPlacedMessageFillsGroup⟩ }, bytes)
  else none

theorem encode_length_pos (message : OrderPlacedMessageFillsGroups) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUIntLE_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : OrderPlacedMessageFillsGroups) : (encode message).length ≤ 1638379 := by
  have bound_orderPlacedMessageFillsGroup := message.orderPlacedMessageFillsGroup.length_lt
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, encodeUIntLE_length, encodeMany_length_const OrderPlacedMessageFillsGroup.encode 25 OrderPlacedMessageFillsGroup.encode_length]
  omega

@[simp] theorem decode_encode (message : OrderPlacedMessageFillsGroups) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeMany_bounded 2 OrderPlacedMessageFillsGroup.encode OrderPlacedMessageFillsGroup.decode OrderPlacedMessageFillsGroup.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.orderPlacedMessageFillsGroup.length_lt]
  rfl

end OrderPlacedMessageFillsGroups

/-- Order Placed Message legs Group: 34 bytes -/
structure OrderPlacedMessageLegsGroup where
  matchId : BitVec 64
  fillId : BitVec 64
  fillPrice : BitVec 64
  fillQty : FillQty
  legSide : BitVec 8
  deriving DecidableEq, Repr

namespace OrderPlacedMessageLegsGroup

def encode (message : OrderPlacedMessageLegsGroup) : List UInt8 :=
  encodeUIntLE 8 message.matchId
    ++ (encodeUIntLE 8 message.fillId
    ++ (encodeUIntLE 8 message.fillPrice
    ++ (FillQty.encode message.fillQty
    ++ (encodeUInt 1 message.legSide))))

def decode (bytes : List UInt8) : Option (OrderPlacedMessageLegsGroup × List UInt8) := do
  let (matchId, bytes) ← decodeUIntLE 8 bytes
  let (fillId, bytes) ← decodeUIntLE 8 bytes
  let (fillPrice, bytes) ← decodeUIntLE 8 bytes
  let (fillQty, bytes) ← FillQty.decode bytes
  let (legSide, bytes) ← decodeUInt 1 bytes
  pure ({ matchId, fillId, fillPrice, fillQty, legSide }, bytes)

@[simp] theorem encode_length (message : OrderPlacedMessageLegsGroup) : (encode message).length = 34 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, FillQty.encode_length, encodeUInt_length]

theorem encode_length_pos (message : OrderPlacedMessageLegsGroup) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OrderPlacedMessageLegsGroup) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, FillQty.decode_encode, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end OrderPlacedMessageLegsGroup

/-- Order Placed Message legs Groups -/
structure OrderPlacedMessageLegsGroups where
  blockLength : BitVec 16
  orderPlacedMessageLegsGroup : Bounded 2 OrderPlacedMessageLegsGroup
  deriving DecidableEq, Repr

namespace OrderPlacedMessageLegsGroups

def encode (message : OrderPlacedMessageLegsGroups) : List UInt8 :=
  encodeUIntLE 2 message.blockLength
    ++ (encodeUIntLE 2 (BitVec.ofNat (8 * 2) message.orderPlacedMessageLegsGroup.val.length)
    ++ (encodeMany OrderPlacedMessageLegsGroup.encode message.orderPlacedMessageLegsGroup.val))

def decode (bytes : List UInt8) : Option (OrderPlacedMessageLegsGroups × List UInt8) := do
  let (blockLength, bytes) ← decodeUIntLE 2 bytes
  let (numInGroup, bytes) ← decodeUIntLE 2 bytes
  let (orderPlacedMessageLegsGroup_, bytes) ← decodeMany OrderPlacedMessageLegsGroup.decode numInGroup.toNat bytes
  if fits_orderPlacedMessageLegsGroup : orderPlacedMessageLegsGroup_.length < 256 ^ 2 then
    pure ({ blockLength, orderPlacedMessageLegsGroup := ⟨orderPlacedMessageLegsGroup_, fits_orderPlacedMessageLegsGroup⟩ }, bytes)
  else none

theorem encode_length_pos (message : OrderPlacedMessageLegsGroups) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUIntLE_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : OrderPlacedMessageLegsGroups) : (encode message).length ≤ 2228194 := by
  have bound_orderPlacedMessageLegsGroup := message.orderPlacedMessageLegsGroup.length_lt
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, encodeUIntLE_length, encodeMany_length_const OrderPlacedMessageLegsGroup.encode 34 OrderPlacedMessageLegsGroup.encode_length]
  omega

@[simp] theorem decode_encode (message : OrderPlacedMessageLegsGroups) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeMany_bounded 2 OrderPlacedMessageLegsGroup.encode OrderPlacedMessageLegsGroup.decode OrderPlacedMessageLegsGroup.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.orderPlacedMessageLegsGroup.length_lt]
  rfl

end OrderPlacedMessageLegsGroups

/-- Order Placed Message -/
structure OrderPlacedMessage where
  timestamp : BitVec 64
  execId : BitVec 64
  clientOrderId : BitVec 64
  orderId : BitVec 64
  instrumentId : BitVec 64
  price : BitVec 64
  quantity : Quantity
  totalFilled : TotalFilled
  visibleQty : VisibleQty
  status : BitVec 8
  cancelReason : BitVec 8
  orderPlacedMessageFillsGroups : OrderPlacedMessageFillsGroups
  orderPlacedMessageLegsGroups : OrderPlacedMessageLegsGroups
  deriving DecidableEq, Repr

namespace OrderPlacedMessage

def encode (message : OrderPlacedMessage) : List UInt8 :=
  encodeUIntLE 8 message.timestamp
    ++ (encodeUIntLE 8 message.execId
    ++ (encodeUIntLE 8 message.clientOrderId
    ++ (encodeUIntLE 8 message.orderId
    ++ (encodeUIntLE 8 message.instrumentId
    ++ (encodeUIntLE 8 message.price
    ++ (Quantity.encode message.quantity
    ++ (TotalFilled.encode message.totalFilled
    ++ (VisibleQty.encode message.visibleQty
    ++ (encodeUInt 1 message.status
    ++ (encodeUInt 1 message.cancelReason
    ++ (OrderPlacedMessageFillsGroups.encode message.orderPlacedMessageFillsGroups
    ++ (OrderPlacedMessageLegsGroups.encode message.orderPlacedMessageLegsGroups))))))))))))

def decode (bytes : List UInt8) : Option (OrderPlacedMessage × List UInt8) := do
  let (timestamp, bytes) ← decodeUIntLE 8 bytes
  let (execId, bytes) ← decodeUIntLE 8 bytes
  let (clientOrderId, bytes) ← decodeUIntLE 8 bytes
  let (orderId, bytes) ← decodeUIntLE 8 bytes
  let (instrumentId, bytes) ← decodeUIntLE 8 bytes
  let (price, bytes) ← decodeUIntLE 8 bytes
  let (quantity, bytes) ← Quantity.decode bytes
  let (totalFilled, bytes) ← TotalFilled.decode bytes
  let (visibleQty, bytes) ← VisibleQty.decode bytes
  let (status, bytes) ← decodeUInt 1 bytes
  let (cancelReason, bytes) ← decodeUInt 1 bytes
  let (orderPlacedMessageFillsGroups, bytes) ← OrderPlacedMessageFillsGroups.decode bytes
  let (orderPlacedMessageLegsGroups, bytes) ← OrderPlacedMessageLegsGroups.decode bytes
  pure ({ timestamp, execId, clientOrderId, orderId, instrumentId, price, quantity, totalFilled, visibleQty, status, cancelReason, orderPlacedMessageFillsGroups, orderPlacedMessageLegsGroups }, bytes)

theorem encode_length_pos (message : OrderPlacedMessage) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUIntLE_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : OrderPlacedMessage) : (encode message).length ≤ 3866650 := by
  have bound_orderPlacedMessageFillsGroups := OrderPlacedMessageFillsGroups.encode_length_le message.orderPlacedMessageFillsGroups
  have bound_orderPlacedMessageLegsGroups := OrderPlacedMessageLegsGroups.encode_length_le message.orderPlacedMessageLegsGroups
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, encodeUIntLE_length, Quantity.encode_length, TotalFilled.encode_length, VisibleQty.encode_length, encodeUInt_length]
  omega

@[simp] theorem decode_encode (message : OrderPlacedMessage) (rest : List UInt8) :
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
  rw [List.append_assoc, Quantity.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, TotalFilled.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, VisibleQty.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, OrderPlacedMessageFillsGroups.decode_encode, some_bind]
  dsimp only
  rw [OrderPlacedMessageLegsGroups.decode_encode, some_bind]
  rfl

end OrderPlacedMessage

/-- Mass Quote Orders Placed Message orders Group: 62 bytes -/
structure MassQuoteOrdersPlacedMessageOrdersGroup where
  clientOrderId : BitVec 64
  orderId : BitVec 64
  instrumentId : BitVec 64
  price : BitVec 64
  quantity : Quantity
  totalFilled : TotalFilled
  visibleQty : VisibleQty
  side : BitVec 8
  status : BitVec 8
  cancelReason : BitVec 8
  deriving DecidableEq, Repr

namespace MassQuoteOrdersPlacedMessageOrdersGroup

def encode (message : MassQuoteOrdersPlacedMessageOrdersGroup) : List UInt8 :=
  encodeUIntLE 8 message.clientOrderId
    ++ (encodeUIntLE 8 message.orderId
    ++ (encodeUIntLE 8 message.instrumentId
    ++ (encodeUIntLE 8 message.price
    ++ (Quantity.encode message.quantity
    ++ (TotalFilled.encode message.totalFilled
    ++ (VisibleQty.encode message.visibleQty
    ++ (encodeUInt 1 message.side
    ++ (encodeUInt 1 message.status
    ++ (encodeUInt 1 message.cancelReason)))))))))

def decode (bytes : List UInt8) : Option (MassQuoteOrdersPlacedMessageOrdersGroup × List UInt8) := do
  let (clientOrderId, bytes) ← decodeUIntLE 8 bytes
  let (orderId, bytes) ← decodeUIntLE 8 bytes
  let (instrumentId, bytes) ← decodeUIntLE 8 bytes
  let (price, bytes) ← decodeUIntLE 8 bytes
  let (quantity, bytes) ← Quantity.decode bytes
  let (totalFilled, bytes) ← TotalFilled.decode bytes
  let (visibleQty, bytes) ← VisibleQty.decode bytes
  let (side, bytes) ← decodeUInt 1 bytes
  let (status, bytes) ← decodeUInt 1 bytes
  let (cancelReason, bytes) ← decodeUInt 1 bytes
  pure ({ clientOrderId, orderId, instrumentId, price, quantity, totalFilled, visibleQty, side, status, cancelReason }, bytes)

@[simp] theorem encode_length (message : MassQuoteOrdersPlacedMessageOrdersGroup) : (encode message).length = 62 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Quantity.encode_length, TotalFilled.encode_length, VisibleQty.encode_length, encodeUInt_length]

theorem encode_length_pos (message : MassQuoteOrdersPlacedMessageOrdersGroup) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : MassQuoteOrdersPlacedMessageOrdersGroup) (rest : List UInt8) :
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
  rw [List.append_assoc, Quantity.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, TotalFilled.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, VisibleQty.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end MassQuoteOrdersPlacedMessageOrdersGroup

/-- Mass Quote Orders Placed Message orders Groups -/
structure MassQuoteOrdersPlacedMessageOrdersGroups where
  blockLength : BitVec 16
  massQuoteOrdersPlacedMessageOrdersGroup : Bounded 2 MassQuoteOrdersPlacedMessageOrdersGroup
  deriving DecidableEq, Repr

namespace MassQuoteOrdersPlacedMessageOrdersGroups

def encode (message : MassQuoteOrdersPlacedMessageOrdersGroups) : List UInt8 :=
  encodeUIntLE 2 message.blockLength
    ++ (encodeUIntLE 2 (BitVec.ofNat (8 * 2) message.massQuoteOrdersPlacedMessageOrdersGroup.val.length)
    ++ (encodeMany MassQuoteOrdersPlacedMessageOrdersGroup.encode message.massQuoteOrdersPlacedMessageOrdersGroup.val))

def decode (bytes : List UInt8) : Option (MassQuoteOrdersPlacedMessageOrdersGroups × List UInt8) := do
  let (blockLength, bytes) ← decodeUIntLE 2 bytes
  let (numInGroup, bytes) ← decodeUIntLE 2 bytes
  let (massQuoteOrdersPlacedMessageOrdersGroup_, bytes) ← decodeMany MassQuoteOrdersPlacedMessageOrdersGroup.decode numInGroup.toNat bytes
  if fits_massQuoteOrdersPlacedMessageOrdersGroup : massQuoteOrdersPlacedMessageOrdersGroup_.length < 256 ^ 2 then
    pure ({ blockLength, massQuoteOrdersPlacedMessageOrdersGroup := ⟨massQuoteOrdersPlacedMessageOrdersGroup_, fits_massQuoteOrdersPlacedMessageOrdersGroup⟩ }, bytes)
  else none

theorem encode_length_pos (message : MassQuoteOrdersPlacedMessageOrdersGroups) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUIntLE_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : MassQuoteOrdersPlacedMessageOrdersGroups) : (encode message).length ≤ 4063174 := by
  have bound_massQuoteOrdersPlacedMessageOrdersGroup := message.massQuoteOrdersPlacedMessageOrdersGroup.length_lt
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, encodeUIntLE_length, encodeMany_length_const MassQuoteOrdersPlacedMessageOrdersGroup.encode 62 MassQuoteOrdersPlacedMessageOrdersGroup.encode_length]
  omega

@[simp] theorem decode_encode (message : MassQuoteOrdersPlacedMessageOrdersGroups) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeMany_bounded 2 MassQuoteOrdersPlacedMessageOrdersGroup.encode MassQuoteOrdersPlacedMessageOrdersGroup.decode MassQuoteOrdersPlacedMessageOrdersGroup.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.massQuoteOrdersPlacedMessageOrdersGroup.length_lt]
  rfl

end MassQuoteOrdersPlacedMessageOrdersGroups

/-- Mass Quote Orders Placed Message fills Group: 33 bytes -/
structure MassQuoteOrdersPlacedMessageFillsGroup where
  matchId : BitVec 64
  orderIdFillId : BitVec 64
  fillPrice : BitVec 64
  fillQty : FillQty
  deriving DecidableEq, Repr

namespace MassQuoteOrdersPlacedMessageFillsGroup

def encode (message : MassQuoteOrdersPlacedMessageFillsGroup) : List UInt8 :=
  encodeUIntLE 8 message.matchId
    ++ (encodeUIntLE 8 message.orderIdFillId
    ++ (encodeUIntLE 8 message.fillPrice
    ++ (FillQty.encode message.fillQty)))

def decode (bytes : List UInt8) : Option (MassQuoteOrdersPlacedMessageFillsGroup × List UInt8) := do
  let (matchId, bytes) ← decodeUIntLE 8 bytes
  let (orderIdFillId, bytes) ← decodeUIntLE 8 bytes
  let (fillPrice, bytes) ← decodeUIntLE 8 bytes
  let (fillQty, bytes) ← FillQty.decode bytes
  pure ({ matchId, orderIdFillId, fillPrice, fillQty }, bytes)

@[simp] theorem encode_length (message : MassQuoteOrdersPlacedMessageFillsGroup) : (encode message).length = 33 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, FillQty.encode_length]

theorem encode_length_pos (message : MassQuoteOrdersPlacedMessageFillsGroup) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : MassQuoteOrdersPlacedMessageFillsGroup) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [FillQty.decode_encode, some_bind]
  rfl

end MassQuoteOrdersPlacedMessageFillsGroup

/-- Mass Quote Orders Placed Message fills Groups -/
structure MassQuoteOrdersPlacedMessageFillsGroups where
  blockLength : BitVec 16
  massQuoteOrdersPlacedMessageFillsGroup : Bounded 2 MassQuoteOrdersPlacedMessageFillsGroup
  deriving DecidableEq, Repr

namespace MassQuoteOrdersPlacedMessageFillsGroups

def encode (message : MassQuoteOrdersPlacedMessageFillsGroups) : List UInt8 :=
  encodeUIntLE 2 message.blockLength
    ++ (encodeUIntLE 2 (BitVec.ofNat (8 * 2) message.massQuoteOrdersPlacedMessageFillsGroup.val.length)
    ++ (encodeMany MassQuoteOrdersPlacedMessageFillsGroup.encode message.massQuoteOrdersPlacedMessageFillsGroup.val))

def decode (bytes : List UInt8) : Option (MassQuoteOrdersPlacedMessageFillsGroups × List UInt8) := do
  let (blockLength, bytes) ← decodeUIntLE 2 bytes
  let (numInGroup, bytes) ← decodeUIntLE 2 bytes
  let (massQuoteOrdersPlacedMessageFillsGroup_, bytes) ← decodeMany MassQuoteOrdersPlacedMessageFillsGroup.decode numInGroup.toNat bytes
  if fits_massQuoteOrdersPlacedMessageFillsGroup : massQuoteOrdersPlacedMessageFillsGroup_.length < 256 ^ 2 then
    pure ({ blockLength, massQuoteOrdersPlacedMessageFillsGroup := ⟨massQuoteOrdersPlacedMessageFillsGroup_, fits_massQuoteOrdersPlacedMessageFillsGroup⟩ }, bytes)
  else none

theorem encode_length_pos (message : MassQuoteOrdersPlacedMessageFillsGroups) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUIntLE_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : MassQuoteOrdersPlacedMessageFillsGroups) : (encode message).length ≤ 2162659 := by
  have bound_massQuoteOrdersPlacedMessageFillsGroup := message.massQuoteOrdersPlacedMessageFillsGroup.length_lt
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, encodeUIntLE_length, encodeMany_length_const MassQuoteOrdersPlacedMessageFillsGroup.encode 33 MassQuoteOrdersPlacedMessageFillsGroup.encode_length]
  omega

@[simp] theorem decode_encode (message : MassQuoteOrdersPlacedMessageFillsGroups) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeMany_bounded 2 MassQuoteOrdersPlacedMessageFillsGroup.encode MassQuoteOrdersPlacedMessageFillsGroup.decode MassQuoteOrdersPlacedMessageFillsGroup.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.massQuoteOrdersPlacedMessageFillsGroup.length_lt]
  rfl

end MassQuoteOrdersPlacedMessageFillsGroups

/-- Mass Quote Orders Placed Message legs Group: 34 bytes -/
structure MassQuoteOrdersPlacedMessageLegsGroup where
  matchId : BitVec 64
  fillId : BitVec 64
  fillPrice : BitVec 64
  fillQty : FillQty
  legSide : BitVec 8
  deriving DecidableEq, Repr

namespace MassQuoteOrdersPlacedMessageLegsGroup

def encode (message : MassQuoteOrdersPlacedMessageLegsGroup) : List UInt8 :=
  encodeUIntLE 8 message.matchId
    ++ (encodeUIntLE 8 message.fillId
    ++ (encodeUIntLE 8 message.fillPrice
    ++ (FillQty.encode message.fillQty
    ++ (encodeUInt 1 message.legSide))))

def decode (bytes : List UInt8) : Option (MassQuoteOrdersPlacedMessageLegsGroup × List UInt8) := do
  let (matchId, bytes) ← decodeUIntLE 8 bytes
  let (fillId, bytes) ← decodeUIntLE 8 bytes
  let (fillPrice, bytes) ← decodeUIntLE 8 bytes
  let (fillQty, bytes) ← FillQty.decode bytes
  let (legSide, bytes) ← decodeUInt 1 bytes
  pure ({ matchId, fillId, fillPrice, fillQty, legSide }, bytes)

@[simp] theorem encode_length (message : MassQuoteOrdersPlacedMessageLegsGroup) : (encode message).length = 34 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, FillQty.encode_length, encodeUInt_length]

theorem encode_length_pos (message : MassQuoteOrdersPlacedMessageLegsGroup) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : MassQuoteOrdersPlacedMessageLegsGroup) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, FillQty.decode_encode, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end MassQuoteOrdersPlacedMessageLegsGroup

/-- Mass Quote Orders Placed Message legs Groups -/
structure MassQuoteOrdersPlacedMessageLegsGroups where
  blockLength : BitVec 16
  massQuoteOrdersPlacedMessageLegsGroup : Bounded 2 MassQuoteOrdersPlacedMessageLegsGroup
  deriving DecidableEq, Repr

namespace MassQuoteOrdersPlacedMessageLegsGroups

def encode (message : MassQuoteOrdersPlacedMessageLegsGroups) : List UInt8 :=
  encodeUIntLE 2 message.blockLength
    ++ (encodeUIntLE 2 (BitVec.ofNat (8 * 2) message.massQuoteOrdersPlacedMessageLegsGroup.val.length)
    ++ (encodeMany MassQuoteOrdersPlacedMessageLegsGroup.encode message.massQuoteOrdersPlacedMessageLegsGroup.val))

def decode (bytes : List UInt8) : Option (MassQuoteOrdersPlacedMessageLegsGroups × List UInt8) := do
  let (blockLength, bytes) ← decodeUIntLE 2 bytes
  let (numInGroup, bytes) ← decodeUIntLE 2 bytes
  let (massQuoteOrdersPlacedMessageLegsGroup_, bytes) ← decodeMany MassQuoteOrdersPlacedMessageLegsGroup.decode numInGroup.toNat bytes
  if fits_massQuoteOrdersPlacedMessageLegsGroup : massQuoteOrdersPlacedMessageLegsGroup_.length < 256 ^ 2 then
    pure ({ blockLength, massQuoteOrdersPlacedMessageLegsGroup := ⟨massQuoteOrdersPlacedMessageLegsGroup_, fits_massQuoteOrdersPlacedMessageLegsGroup⟩ }, bytes)
  else none

theorem encode_length_pos (message : MassQuoteOrdersPlacedMessageLegsGroups) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUIntLE_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : MassQuoteOrdersPlacedMessageLegsGroups) : (encode message).length ≤ 2228194 := by
  have bound_massQuoteOrdersPlacedMessageLegsGroup := message.massQuoteOrdersPlacedMessageLegsGroup.length_lt
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, encodeUIntLE_length, encodeMany_length_const MassQuoteOrdersPlacedMessageLegsGroup.encode 34 MassQuoteOrdersPlacedMessageLegsGroup.encode_length]
  omega

@[simp] theorem decode_encode (message : MassQuoteOrdersPlacedMessageLegsGroups) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeMany_bounded 2 MassQuoteOrdersPlacedMessageLegsGroup.encode MassQuoteOrdersPlacedMessageLegsGroup.decode MassQuoteOrdersPlacedMessageLegsGroup.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.massQuoteOrdersPlacedMessageLegsGroup.length_lt]
  rfl

end MassQuoteOrdersPlacedMessageLegsGroups

/-- Mass Quote Orders Placed Message -/
structure MassQuoteOrdersPlacedMessage where
  timestamp : BitVec 64
  execId : BitVec 64
  mmpGroupId : BitVec 64
  massQuoteOrdersPlacedMessageOrdersGroups : MassQuoteOrdersPlacedMessageOrdersGroups
  massQuoteOrdersPlacedMessageFillsGroups : MassQuoteOrdersPlacedMessageFillsGroups
  massQuoteOrdersPlacedMessageLegsGroups : MassQuoteOrdersPlacedMessageLegsGroups
  deriving DecidableEq, Repr

namespace MassQuoteOrdersPlacedMessage

def encode (message : MassQuoteOrdersPlacedMessage) : List UInt8 :=
  encodeUIntLE 8 message.timestamp
    ++ (encodeUIntLE 8 message.execId
    ++ (encodeUIntLE 8 message.mmpGroupId
    ++ (MassQuoteOrdersPlacedMessageOrdersGroups.encode message.massQuoteOrdersPlacedMessageOrdersGroups
    ++ (MassQuoteOrdersPlacedMessageFillsGroups.encode message.massQuoteOrdersPlacedMessageFillsGroups
    ++ (MassQuoteOrdersPlacedMessageLegsGroups.encode message.massQuoteOrdersPlacedMessageLegsGroups)))))

def decode (bytes : List UInt8) : Option (MassQuoteOrdersPlacedMessage × List UInt8) := do
  let (timestamp, bytes) ← decodeUIntLE 8 bytes
  let (execId, bytes) ← decodeUIntLE 8 bytes
  let (mmpGroupId, bytes) ← decodeUIntLE 8 bytes
  let (massQuoteOrdersPlacedMessageOrdersGroups, bytes) ← MassQuoteOrdersPlacedMessageOrdersGroups.decode bytes
  let (massQuoteOrdersPlacedMessageFillsGroups, bytes) ← MassQuoteOrdersPlacedMessageFillsGroups.decode bytes
  let (massQuoteOrdersPlacedMessageLegsGroups, bytes) ← MassQuoteOrdersPlacedMessageLegsGroups.decode bytes
  pure ({ timestamp, execId, mmpGroupId, massQuoteOrdersPlacedMessageOrdersGroups, massQuoteOrdersPlacedMessageFillsGroups, massQuoteOrdersPlacedMessageLegsGroups }, bytes)

theorem encode_length_pos (message : MassQuoteOrdersPlacedMessage) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUIntLE_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : MassQuoteOrdersPlacedMessage) : (encode message).length ≤ 8454051 := by
  have bound_massQuoteOrdersPlacedMessageOrdersGroups := MassQuoteOrdersPlacedMessageOrdersGroups.encode_length_le message.massQuoteOrdersPlacedMessageOrdersGroups
  have bound_massQuoteOrdersPlacedMessageFillsGroups := MassQuoteOrdersPlacedMessageFillsGroups.encode_length_le message.massQuoteOrdersPlacedMessageFillsGroups
  have bound_massQuoteOrdersPlacedMessageLegsGroups := MassQuoteOrdersPlacedMessageLegsGroups.encode_length_le message.massQuoteOrdersPlacedMessageLegsGroups
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, encodeUIntLE_length]
  omega

@[simp] theorem decode_encode (message : MassQuoteOrdersPlacedMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, MassQuoteOrdersPlacedMessageOrdersGroups.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, MassQuoteOrdersPlacedMessageFillsGroups.decode_encode, some_bind]
  dsimp only
  rw [MassQuoteOrdersPlacedMessageLegsGroups.decode_encode, some_bind]
  rfl

end MassQuoteOrdersPlacedMessage

/-- Mass Quote Mmp Triggered Message: 57 bytes -/
structure MassQuoteMmpTriggeredMessage where
  timestamp : BitVec 64
  execId : BitVec 64
  mmpGroupId : BitVec 64
  frozenUntil : BitVec 64
  quantityLevel : Alpha 8
  vegaLevel : Alpha 8
  deltaLevel : Alpha 8
  trigger : BitVec 8
  deriving DecidableEq, Repr

namespace MassQuoteMmpTriggeredMessage

def encode (message : MassQuoteMmpTriggeredMessage) : List UInt8 :=
  encodeUIntLE 8 message.timestamp
    ++ (encodeUIntLE 8 message.execId
    ++ (encodeUIntLE 8 message.mmpGroupId
    ++ (encodeUIntLE 8 message.frozenUntil
    ++ (Alpha.encode message.quantityLevel
    ++ (Alpha.encode message.vegaLevel
    ++ (Alpha.encode message.deltaLevel
    ++ (encodeUInt 1 message.trigger)))))))

def decode (bytes : List UInt8) : Option (MassQuoteMmpTriggeredMessage × List UInt8) := do
  let (timestamp, bytes) ← decodeUIntLE 8 bytes
  let (execId, bytes) ← decodeUIntLE 8 bytes
  let (mmpGroupId, bytes) ← decodeUIntLE 8 bytes
  let (frozenUntil, bytes) ← decodeUIntLE 8 bytes
  let (quantityLevel, bytes) ← Alpha.decode 8 bytes
  let (vegaLevel, bytes) ← Alpha.decode 8 bytes
  let (deltaLevel, bytes) ← Alpha.decode 8 bytes
  let (trigger, bytes) ← decodeUInt 1 bytes
  pure ({ timestamp, execId, mmpGroupId, frozenUntil, quantityLevel, vegaLevel, deltaLevel, trigger }, bytes)

@[simp] theorem encode_length (message : MassQuoteMmpTriggeredMessage) : (encode message).length = 57 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length, encodeUInt_length]

theorem encode_length_pos (message : MassQuoteMmpTriggeredMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : MassQuoteMmpTriggeredMessage) (rest : List UInt8) :
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
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end MassQuoteMmpTriggeredMessage

/-- Orders Mmp Triggered Message: 57 bytes -/
structure OrdersMmpTriggeredMessage where
  timestamp : BitVec 64
  execId : BitVec 64
  currencyPairId : BitVec 64
  frozenUntil : BitVec 64
  quantityLevel : Alpha 8
  vegaLevel : Alpha 8
  deltaLevel : Alpha 8
  trigger : BitVec 8
  deriving DecidableEq, Repr

namespace OrdersMmpTriggeredMessage

def encode (message : OrdersMmpTriggeredMessage) : List UInt8 :=
  encodeUIntLE 8 message.timestamp
    ++ (encodeUIntLE 8 message.execId
    ++ (encodeUIntLE 8 message.currencyPairId
    ++ (encodeUIntLE 8 message.frozenUntil
    ++ (Alpha.encode message.quantityLevel
    ++ (Alpha.encode message.vegaLevel
    ++ (Alpha.encode message.deltaLevel
    ++ (encodeUInt 1 message.trigger)))))))

def decode (bytes : List UInt8) : Option (OrdersMmpTriggeredMessage × List UInt8) := do
  let (timestamp, bytes) ← decodeUIntLE 8 bytes
  let (execId, bytes) ← decodeUIntLE 8 bytes
  let (currencyPairId, bytes) ← decodeUIntLE 8 bytes
  let (frozenUntil, bytes) ← decodeUIntLE 8 bytes
  let (quantityLevel, bytes) ← Alpha.decode 8 bytes
  let (vegaLevel, bytes) ← Alpha.decode 8 bytes
  let (deltaLevel, bytes) ← Alpha.decode 8 bytes
  let (trigger, bytes) ← decodeUInt 1 bytes
  pure ({ timestamp, execId, currencyPairId, frozenUntil, quantityLevel, vegaLevel, deltaLevel, trigger }, bytes)

@[simp] theorem encode_length (message : OrdersMmpTriggeredMessage) : (encode message).length = 57 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length, encodeUInt_length]

theorem encode_length_pos (message : OrdersMmpTriggeredMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OrdersMmpTriggeredMessage) (rest : List UInt8) :
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
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end OrdersMmpTriggeredMessage

/-- Mass Quote Mmp Unfrozen Message: 32 bytes -/
structure MassQuoteMmpUnfrozenMessage where
  timestamp : BitVec 64
  execId : BitVec 64
  mmpGroupId : BitVec 64
  correlationIdOptional : BitVec 64
  deriving DecidableEq, Repr

namespace MassQuoteMmpUnfrozenMessage

def encode (message : MassQuoteMmpUnfrozenMessage) : List UInt8 :=
  encodeUIntLE 8 message.timestamp
    ++ (encodeUIntLE 8 message.execId
    ++ (encodeUIntLE 8 message.mmpGroupId
    ++ (encodeUIntLE 8 message.correlationIdOptional)))

def decode (bytes : List UInt8) : Option (MassQuoteMmpUnfrozenMessage × List UInt8) := do
  let (timestamp, bytes) ← decodeUIntLE 8 bytes
  let (execId, bytes) ← decodeUIntLE 8 bytes
  let (mmpGroupId, bytes) ← decodeUIntLE 8 bytes
  let (correlationIdOptional, bytes) ← decodeUIntLE 8 bytes
  pure ({ timestamp, execId, mmpGroupId, correlationIdOptional }, bytes)

@[simp] theorem encode_length (message : MassQuoteMmpUnfrozenMessage) : (encode message).length = 32 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length]

theorem encode_length_pos (message : MassQuoteMmpUnfrozenMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : MassQuoteMmpUnfrozenMessage) (rest : List UInt8) :
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

end MassQuoteMmpUnfrozenMessage

/-- Orders Mmp Unfrozen Message: 32 bytes -/
structure OrdersMmpUnfrozenMessage where
  timestamp : BitVec 64
  execId : BitVec 64
  currencyPairId : BitVec 64
  correlationIdOptional : BitVec 64
  deriving DecidableEq, Repr

namespace OrdersMmpUnfrozenMessage

def encode (message : OrdersMmpUnfrozenMessage) : List UInt8 :=
  encodeUIntLE 8 message.timestamp
    ++ (encodeUIntLE 8 message.execId
    ++ (encodeUIntLE 8 message.currencyPairId
    ++ (encodeUIntLE 8 message.correlationIdOptional)))

def decode (bytes : List UInt8) : Option (OrdersMmpUnfrozenMessage × List UInt8) := do
  let (timestamp, bytes) ← decodeUIntLE 8 bytes
  let (execId, bytes) ← decodeUIntLE 8 bytes
  let (currencyPairId, bytes) ← decodeUIntLE 8 bytes
  let (correlationIdOptional, bytes) ← decodeUIntLE 8 bytes
  pure ({ timestamp, execId, currencyPairId, correlationIdOptional }, bytes)

@[simp] theorem encode_length (message : OrdersMmpUnfrozenMessage) : (encode message).length = 32 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length]

theorem encode_length_pos (message : OrdersMmpUnfrozenMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OrdersMmpUnfrozenMessage) (rest : List UInt8) :
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

end OrdersMmpUnfrozenMessage

/-- Any Payload, selected by Template Id -/
inductive Payload where
  | logonMessage (message : LogonMessage) -- 1
  | logonConfMessage (message : LogonConfMessage) -- 2
  | logoutMessage (message : LogoutMessage) -- 4
  | loggedOutMessage (message : LoggedOutMessage) -- 5
  | heartbeatMessage (message : HeartbeatMessage) -- 10
  | testRequestMessage (message : TestRequestMessage) -- 11
  | resendRequestMessage (message : ResendRequestMessage) -- 20
  | gapFillMessage (message : GapFillMessage) -- 21
  | rejectMessage (message : RejectMessage) -- 30
  | newOrderRequestMessage (message : NewOrderRequestMessage) -- 100
  | amendOrderRequestMessage (message : AmendOrderRequestMessage) -- 110
  | cancelOrderRequestMessage (message : CancelOrderRequestMessage) -- 120
  | massQuoteRequestMessage (message : MassQuoteRequestMessage) -- 130
  | massCancelRequestMessage (message : MassCancelRequestMessage) -- 140
  | massQuoteCancelRequestMessage (message : MassQuoteCancelRequestMessage) -- 145
  | newOrderResponseMessage (message : NewOrderResponseMessage) -- 200
  | newOrderRejectMessage (message : NewOrderRejectMessage) -- 202
  | amendOrderResponseMessage (message : AmendOrderResponseMessage) -- 210
  | amendOrderRejectMessage (message : AmendOrderRejectMessage) -- 212
  | cancelOrderResponseMessage (message : CancelOrderResponseMessage) -- 220
  | cancelOrderRejectMessage (message : CancelOrderRejectMessage) -- 222
  | massQuoteResponseMessage (message : MassQuoteResponseMessage) -- 230
  | massQuoteRejectMessage (message : MassQuoteRejectMessage) -- 232
  | massCancelResponseMessage (message : MassCancelResponseMessage) -- 240
  | massCancelRejectMessage (message : MassCancelRejectMessage) -- 242
  | orderFilledMessage (message : OrderFilledMessage) -- 300
  | ordersCanceledMessage (message : OrdersCanceledMessage) -- 310
  | orderPlacedMessage (message : OrderPlacedMessage) -- 312
  | massQuoteOrdersPlacedMessage (message : MassQuoteOrdersPlacedMessage) -- 314
  | massQuoteMmpTriggeredMessage (message : MassQuoteMmpTriggeredMessage) -- 320
  | ordersMmpTriggeredMessage (message : OrdersMmpTriggeredMessage) -- 322
  | massQuoteMmpUnfrozenMessage (message : MassQuoteMmpUnfrozenMessage) -- 324
  | ordersMmpUnfrozenMessage (message : OrdersMmpUnfrozenMessage) -- 326
  deriving DecidableEq, Repr

namespace Payload

/-- The Template Id each message is sent under -/
def tag : Payload → BitVec 16
  | .logonMessage _ => 1
  | .logonConfMessage _ => 2
  | .logoutMessage _ => 4
  | .loggedOutMessage _ => 5
  | .heartbeatMessage _ => 10
  | .testRequestMessage _ => 11
  | .resendRequestMessage _ => 20
  | .gapFillMessage _ => 21
  | .rejectMessage _ => 30
  | .newOrderRequestMessage _ => 100
  | .amendOrderRequestMessage _ => 110
  | .cancelOrderRequestMessage _ => 120
  | .massQuoteRequestMessage _ => 130
  | .massCancelRequestMessage _ => 140
  | .massQuoteCancelRequestMessage _ => 145
  | .newOrderResponseMessage _ => 200
  | .newOrderRejectMessage _ => 202
  | .amendOrderResponseMessage _ => 210
  | .amendOrderRejectMessage _ => 212
  | .cancelOrderResponseMessage _ => 220
  | .cancelOrderRejectMessage _ => 222
  | .massQuoteResponseMessage _ => 230
  | .massQuoteRejectMessage _ => 232
  | .massCancelResponseMessage _ => 240
  | .massCancelRejectMessage _ => 242
  | .orderFilledMessage _ => 300
  | .ordersCanceledMessage _ => 310
  | .orderPlacedMessage _ => 312
  | .massQuoteOrdersPlacedMessage _ => 314
  | .massQuoteMmpTriggeredMessage _ => 320
  | .ordersMmpTriggeredMessage _ => 322
  | .massQuoteMmpUnfrozenMessage _ => 324
  | .ordersMmpUnfrozenMessage _ => 326

def encode : Payload → List UInt8
  | .logonMessage message => LogonMessage.encode message
  | .logonConfMessage message => LogonConfMessage.encode message
  | .logoutMessage message => LogoutMessage.encode message
  | .loggedOutMessage message => LoggedOutMessage.encode message
  | .heartbeatMessage message => HeartbeatMessage.encode message
  | .testRequestMessage message => TestRequestMessage.encode message
  | .resendRequestMessage message => ResendRequestMessage.encode message
  | .gapFillMessage message => GapFillMessage.encode message
  | .rejectMessage message => RejectMessage.encode message
  | .newOrderRequestMessage message => NewOrderRequestMessage.encode message
  | .amendOrderRequestMessage message => AmendOrderRequestMessage.encode message
  | .cancelOrderRequestMessage message => CancelOrderRequestMessage.encode message
  | .massQuoteRequestMessage message => MassQuoteRequestMessage.encode message
  | .massCancelRequestMessage message => MassCancelRequestMessage.encode message
  | .massQuoteCancelRequestMessage message => MassQuoteCancelRequestMessage.encode message
  | .newOrderResponseMessage message => NewOrderResponseMessage.encode message
  | .newOrderRejectMessage message => NewOrderRejectMessage.encode message
  | .amendOrderResponseMessage message => AmendOrderResponseMessage.encode message
  | .amendOrderRejectMessage message => AmendOrderRejectMessage.encode message
  | .cancelOrderResponseMessage message => CancelOrderResponseMessage.encode message
  | .cancelOrderRejectMessage message => CancelOrderRejectMessage.encode message
  | .massQuoteResponseMessage message => MassQuoteResponseMessage.encode message
  | .massQuoteRejectMessage message => MassQuoteRejectMessage.encode message
  | .massCancelResponseMessage message => MassCancelResponseMessage.encode message
  | .massCancelRejectMessage message => MassCancelRejectMessage.encode message
  | .orderFilledMessage message => OrderFilledMessage.encode message
  | .ordersCanceledMessage message => OrdersCanceledMessage.encode message
  | .orderPlacedMessage message => OrderPlacedMessage.encode message
  | .massQuoteOrdersPlacedMessage message => MassQuoteOrdersPlacedMessage.encode message
  | .massQuoteMmpTriggeredMessage message => MassQuoteMmpTriggeredMessage.encode message
  | .ordersMmpTriggeredMessage message => OrdersMmpTriggeredMessage.encode message
  | .massQuoteMmpUnfrozenMessage message => MassQuoteMmpUnfrozenMessage.encode message
  | .ordersMmpUnfrozenMessage message => OrdersMmpUnfrozenMessage.encode message

/-- The most bytes any message's encoding can take -/
theorem encode_length_le (message : Payload) : (encode message).length ≤ 11796364 := by
  cases message with
  | logonMessage inner =>
    simp only [encode, LogonMessage.encode_length]
    omega
  | logonConfMessage inner =>
    simp only [encode, LogonConfMessage.encode_length]
    omega
  | logoutMessage inner =>
    have bound_inner := LogoutMessage.encode_length_le inner
    simp only [encode]
    omega
  | loggedOutMessage inner =>
    have bound_inner := LoggedOutMessage.encode_length_le inner
    simp only [encode]
    omega
  | heartbeatMessage inner =>
    simp only [encode, HeartbeatMessage.encode_length]
    omega
  | testRequestMessage inner =>
    simp only [encode, TestRequestMessage.encode_length]
    omega
  | resendRequestMessage inner =>
    simp only [encode, ResendRequestMessage.encode_length]
    omega
  | gapFillMessage inner =>
    simp only [encode, GapFillMessage.encode_length]
    omega
  | rejectMessage inner =>
    have bound_inner := RejectMessage.encode_length_le inner
    simp only [encode]
    omega
  | newOrderRequestMessage inner =>
    simp only [encode, NewOrderRequestMessage.encode_length]
    omega
  | amendOrderRequestMessage inner =>
    simp only [encode, AmendOrderRequestMessage.encode_length]
    omega
  | cancelOrderRequestMessage inner =>
    simp only [encode, CancelOrderRequestMessage.encode_length]
    omega
  | massQuoteRequestMessage inner =>
    have bound_inner := MassQuoteRequestMessage.encode_length_le inner
    simp only [encode]
    omega
  | massCancelRequestMessage inner =>
    simp only [encode, MassCancelRequestMessage.encode_length]
    omega
  | massQuoteCancelRequestMessage inner =>
    simp only [encode, MassQuoteCancelRequestMessage.encode_length]
    omega
  | newOrderResponseMessage inner =>
    have bound_inner := NewOrderResponseMessage.encode_length_le inner
    simp only [encode]
    omega
  | newOrderRejectMessage inner =>
    have bound_inner := NewOrderRejectMessage.encode_length_le inner
    simp only [encode]
    omega
  | amendOrderResponseMessage inner =>
    have bound_inner := AmendOrderResponseMessage.encode_length_le inner
    simp only [encode]
    omega
  | amendOrderRejectMessage inner =>
    have bound_inner := AmendOrderRejectMessage.encode_length_le inner
    simp only [encode]
    omega
  | cancelOrderResponseMessage inner =>
    simp only [encode, CancelOrderResponseMessage.encode_length]
    omega
  | cancelOrderRejectMessage inner =>
    have bound_inner := CancelOrderRejectMessage.encode_length_le inner
    simp only [encode]
    omega
  | massQuoteResponseMessage inner =>
    have bound_inner := MassQuoteResponseMessage.encode_length_le inner
    simp only [encode]
    omega
  | massQuoteRejectMessage inner =>
    have bound_inner := MassQuoteRejectMessage.encode_length_le inner
    simp only [encode]
    omega
  | massCancelResponseMessage inner =>
    simp only [encode, MassCancelResponseMessage.encode_length]
    omega
  | massCancelRejectMessage inner =>
    have bound_inner := MassCancelRejectMessage.encode_length_le inner
    simp only [encode]
    omega
  | orderFilledMessage inner =>
    have bound_inner := OrderFilledMessage.encode_length_le inner
    simp only [encode]
    omega
  | ordersCanceledMessage inner =>
    have bound_inner := OrdersCanceledMessage.encode_length_le inner
    simp only [encode]
    omega
  | orderPlacedMessage inner =>
    have bound_inner := OrderPlacedMessage.encode_length_le inner
    simp only [encode]
    omega
  | massQuoteOrdersPlacedMessage inner =>
    have bound_inner := MassQuoteOrdersPlacedMessage.encode_length_le inner
    simp only [encode]
    omega
  | massQuoteMmpTriggeredMessage inner =>
    simp only [encode, MassQuoteMmpTriggeredMessage.encode_length]
    omega
  | ordersMmpTriggeredMessage inner =>
    simp only [encode, OrdersMmpTriggeredMessage.encode_length]
    omega
  | massQuoteMmpUnfrozenMessage inner =>
    simp only [encode, MassQuoteMmpUnfrozenMessage.encode_length]
    omega
  | ordersMmpUnfrozenMessage inner =>
    simp only [encode, OrdersMmpUnfrozenMessage.encode_length]
    omega

def decode (tag : BitVec 16) (bytes : List UInt8) : Option (Payload × List UInt8) :=
  if tag = 1 then (LogonMessage.decode bytes).map fun (message, rest) => (.logonMessage message, rest)
  else if tag = 2 then (LogonConfMessage.decode bytes).map fun (message, rest) => (.logonConfMessage message, rest)
  else if tag = 4 then (LogoutMessage.decode bytes).map fun (message, rest) => (.logoutMessage message, rest)
  else if tag = 5 then (LoggedOutMessage.decode bytes).map fun (message, rest) => (.loggedOutMessage message, rest)
  else if tag = 10 then (HeartbeatMessage.decode bytes).map fun (message, rest) => (.heartbeatMessage message, rest)
  else if tag = 11 then (TestRequestMessage.decode bytes).map fun (message, rest) => (.testRequestMessage message, rest)
  else if tag = 20 then (ResendRequestMessage.decode bytes).map fun (message, rest) => (.resendRequestMessage message, rest)
  else if tag = 21 then (GapFillMessage.decode bytes).map fun (message, rest) => (.gapFillMessage message, rest)
  else if tag = 30 then (RejectMessage.decode bytes).map fun (message, rest) => (.rejectMessage message, rest)
  else if tag = 100 then (NewOrderRequestMessage.decode bytes).map fun (message, rest) => (.newOrderRequestMessage message, rest)
  else if tag = 110 then (AmendOrderRequestMessage.decode bytes).map fun (message, rest) => (.amendOrderRequestMessage message, rest)
  else if tag = 120 then (CancelOrderRequestMessage.decode bytes).map fun (message, rest) => (.cancelOrderRequestMessage message, rest)
  else if tag = 130 then (MassQuoteRequestMessage.decode bytes).map fun (message, rest) => (.massQuoteRequestMessage message, rest)
  else if tag = 140 then (MassCancelRequestMessage.decode bytes).map fun (message, rest) => (.massCancelRequestMessage message, rest)
  else if tag = 145 then (MassQuoteCancelRequestMessage.decode bytes).map fun (message, rest) => (.massQuoteCancelRequestMessage message, rest)
  else if tag = 200 then (NewOrderResponseMessage.decode bytes).map fun (message, rest) => (.newOrderResponseMessage message, rest)
  else if tag = 202 then (NewOrderRejectMessage.decode bytes).map fun (message, rest) => (.newOrderRejectMessage message, rest)
  else if tag = 210 then (AmendOrderResponseMessage.decode bytes).map fun (message, rest) => (.amendOrderResponseMessage message, rest)
  else if tag = 212 then (AmendOrderRejectMessage.decode bytes).map fun (message, rest) => (.amendOrderRejectMessage message, rest)
  else if tag = 220 then (CancelOrderResponseMessage.decode bytes).map fun (message, rest) => (.cancelOrderResponseMessage message, rest)
  else if tag = 222 then (CancelOrderRejectMessage.decode bytes).map fun (message, rest) => (.cancelOrderRejectMessage message, rest)
  else if tag = 230 then (MassQuoteResponseMessage.decode bytes).map fun (message, rest) => (.massQuoteResponseMessage message, rest)
  else if tag = 232 then (MassQuoteRejectMessage.decode bytes).map fun (message, rest) => (.massQuoteRejectMessage message, rest)
  else if tag = 240 then (MassCancelResponseMessage.decode bytes).map fun (message, rest) => (.massCancelResponseMessage message, rest)
  else if tag = 242 then (MassCancelRejectMessage.decode bytes).map fun (message, rest) => (.massCancelRejectMessage message, rest)
  else if tag = 300 then (OrderFilledMessage.decode bytes).map fun (message, rest) => (.orderFilledMessage message, rest)
  else if tag = 310 then (OrdersCanceledMessage.decode bytes).map fun (message, rest) => (.ordersCanceledMessage message, rest)
  else if tag = 312 then (OrderPlacedMessage.decode bytes).map fun (message, rest) => (.orderPlacedMessage message, rest)
  else if tag = 314 then (MassQuoteOrdersPlacedMessage.decode bytes).map fun (message, rest) => (.massQuoteOrdersPlacedMessage message, rest)
  else if tag = 320 then (MassQuoteMmpTriggeredMessage.decode bytes).map fun (message, rest) => (.massQuoteMmpTriggeredMessage message, rest)
  else if tag = 322 then (OrdersMmpTriggeredMessage.decode bytes).map fun (message, rest) => (.ordersMmpTriggeredMessage message, rest)
  else if tag = 324 then (MassQuoteMmpUnfrozenMessage.decode bytes).map fun (message, rest) => (.massQuoteMmpUnfrozenMessage message, rest)
  else if tag = 326 then (OrdersMmpUnfrozenMessage.decode bytes).map fun (message, rest) => (.ordersMmpUnfrozenMessage message, rest)
  else none

@[simp] theorem decode_encode (message : Payload) (rest : List UInt8) :
    decode (tag message) (encode message ++ rest) = some (message, rest) := by
  cases message <;> simp [decode, encode, tag]

end Payload

/-- Sbe Message: the body, which the record carries with the proof it fits its frame -/
structure SbeMessageBody where
  protocolId : BitVec 8
  sessionFlags : BitVec 8
  schemaVersion : BitVec 16
  sequenceNumber : BitVec 64
  lastProcessedSeqNo : BitVec 64
  sendTimeNs : BitVec 64
  payload : Payload
  padding : Capped 65531
  deriving DecidableEq, Repr

namespace SbeMessageBody

def encodeBody (message : SbeMessageBody) : List UInt8 :=
  encodeUIntLE 2 (Payload.tag message.payload)
    ++ (encodeUIntLE 2 message.schemaVersion
    ++ (encodeUIntLE 8 message.sequenceNumber
    ++ (encodeUIntLE 8 message.lastProcessedSeqNo
    ++ (encodeUIntLE 8 message.sendTimeNs
    ++ (Payload.encode message.payload
    ++ (message.padding.val))))))

def decodeBody (protocolId : BitVec 8) (sessionFlags : BitVec 8) (bytes : List UInt8) : Option SbeMessageBody := do
  let (templateId, bytes) ← decodeUIntLE 2 bytes
  let (schemaVersion, bytes) ← decodeUIntLE 2 bytes
  let (sequenceNumber, bytes) ← decodeUIntLE 8 bytes
  let (lastProcessedSeqNo, bytes) ← decodeUIntLE 8 bytes
  let (sendTimeNs, bytes) ← decodeUIntLE 8 bytes
  let (payload, bytes) ← Payload.decode templateId bytes
  let padding_ := bytes
  if fits_padding : padding_.length ≤ 65531 then
    pure { protocolId, sessionFlags, schemaVersion, sequenceNumber, lastProcessedSeqNo, sendTimeNs, payload, padding := ⟨padding_, fits_padding⟩ }
  else none

theorem decodeBody_encodeBody (message : SbeMessageBody) : decodeBody message.protocolId message.sessionFlags (encodeBody message) = some message := by
  unfold decodeBody encodeBody
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [Payload.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.padding.length_le]
  rfl

end SbeMessageBody

/-- Sbe Message: the body with the proof its encoding fits Message Length, whose 2 bytes no bound of the fields fits -/
abbrev SbeMessage := Fitting SbeMessageBody.encodeBody 4 65536

namespace SbeMessage

def encode (message : SbeMessage) : List UInt8 :=
  encodeUInt 1 message.val.protocolId
    ++ (encodeUIntLE 1 message.val.sessionFlags
    ++ (encodeFramedLE 2 4 SbeMessageBody.encodeBody message.val))

def decode (bytes : List UInt8) : Option (SbeMessage × List UInt8) := do
  let (protocolId, bytes) ← decodeUInt 1 bytes
  let (sessionFlags, bytes) ← decodeUIntLE 1 bytes
  decodeFittingAllLE 2 4 SbeMessageBody.encodeBody (SbeMessageBody.decodeBody protocolId sessionFlags) bytes

@[simp] theorem decode_encode (message : SbeMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  exact decodeFittingAllLE_encodeFramedLE 2 4 SbeMessageBody.encodeBody (SbeMessageBody.decodeBody message.val.protocolId message.val.sessionFlags) message (SbeMessageBody.decodeBody_encodeBody message.val) rest

theorem encode_length_pos (message : SbeMessage) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUInt_length, encodeUIntLE_length, List.length_append, ← Nat.add_assoc, encodeFramedLE_length]
  omega

/-- The most bytes an encoding can take: what the prefix can count, by the fit the message carries -/
theorem encode_length_le (message : SbeMessage) : (encode message).length ≤ 65535 := by
  have fits := message.fits
  unfold encode
  simp only [encodeUInt_length, encodeUIntLE_length, List.length_append, ← Nat.add_assoc, encodeFramedLE_length]
  omega

end SbeMessage

/-- Packet -/
structure Packet where
  sbeMessage : List SbeMessage
  deriving DecidableEq, Repr

namespace Packet

def encode (message : Packet) : List UInt8 :=
  encodeMany SbeMessage.encode message.sbeMessage

def decode (bytes : List UInt8) : Option Packet := do
  let sbeMessage ← decodeAll SbeMessage.decode bytes.length bytes
  pure { sbeMessage }

theorem decode_encode (message : Packet) : decode (encode message) = some message := by
  unfold decode encode
  rw [decodeAll_encodeMany SbeMessage.encode SbeMessage.decode SbeMessage.decode_encode SbeMessage.encode_length_pos message.sbeMessage _ (encodeMany_length_ge SbeMessage.encode SbeMessage.encode_length_pos message.sbeMessage), some_bind]
  rfl

end Packet

end Omi.CoinbaseDeribitOrdersapiSbeV10
