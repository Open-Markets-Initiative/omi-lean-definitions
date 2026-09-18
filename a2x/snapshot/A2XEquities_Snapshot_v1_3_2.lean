import Omi.Wire

/-!
# A2X Markets Snapshot Feed v1.3.2

Generated from the binary model, with the proofs the model's rules call for: every record
decodes back to what was encoded; a message dispatch selects the message its type names;
a count is written from the list it counts; a length prefix is written from the bytes it frames;
and a packet read to the end of its data decodes to the messages that were written.

Note: Market Flags is a bit field set, proven as its 1 byte integer rather than bit by bit.

Text fields are kept byte for byte, padding included, so what is decoded encodes back unchanged.
Prices with implied decimals are proven as the integers on the wire.
-/

namespace Omi.A2xA2xequitiesSnapshotAmdV132

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

/-- Snapshot Start Message: 14 bytes -/
structure SnapshotStartMessage where
  streamSeqNo : BitVec 32
  securityCount : BitVec 16
  timestamp : BitVec 64
  deriving DecidableEq, Repr

namespace SnapshotStartMessage

def encode (message : SnapshotStartMessage) : List UInt8 :=
  encodeUIntLE 4 message.streamSeqNo
    ++ (encodeUIntLE 2 message.securityCount
    ++ (encodeUIntLE 8 message.timestamp))

def decode (bytes : List UInt8) : Option (SnapshotStartMessage × List UInt8) := do
  let (streamSeqNo, bytes) ← decodeUIntLE 4 bytes
  let (securityCount, bytes) ← decodeUIntLE 2 bytes
  let (timestamp, bytes) ← decodeUIntLE 8 bytes
  pure ({ streamSeqNo, securityCount, timestamp }, bytes)

@[simp] theorem encode_length (message : SnapshotStartMessage) : (encode message).length = 14 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length]

theorem encode_length_pos (message : SnapshotStartMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SnapshotStartMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end SnapshotStartMessage

/-- Book Status Message: 22 bytes -/
structure BookStatusMessage where
  securityId : BitVec 16
  tradingStatus : BitVec 8
  marketFlags : BitVec 8
  entries : BitVec 16
  closingBuyQty : BitVec 32
  closingSellQty : BitVec 32
  indicativePrice : BitVec 64
  deriving DecidableEq, Repr

namespace BookStatusMessage

def encode (message : BookStatusMessage) : List UInt8 :=
  encodeUIntLE 2 message.securityId
    ++ (encodeUIntLE 1 message.tradingStatus
    ++ (encodeUIntLE 1 message.marketFlags
    ++ (encodeUIntLE 2 message.entries
    ++ (encodeUIntLE 4 message.closingBuyQty
    ++ (encodeUIntLE 4 message.closingSellQty
    ++ (encodeUIntLE 8 message.indicativePrice))))))

def decode (bytes : List UInt8) : Option (BookStatusMessage × List UInt8) := do
  let (securityId, bytes) ← decodeUIntLE 2 bytes
  let (tradingStatus, bytes) ← decodeUIntLE 1 bytes
  let (marketFlags, bytes) ← decodeUIntLE 1 bytes
  let (entries, bytes) ← decodeUIntLE 2 bytes
  let (closingBuyQty, bytes) ← decodeUIntLE 4 bytes
  let (closingSellQty, bytes) ← decodeUIntLE 4 bytes
  let (indicativePrice, bytes) ← decodeUIntLE 8 bytes
  pure ({ securityId, tradingStatus, marketFlags, entries, closingBuyQty, closingSellQty, indicativePrice }, bytes)

@[simp] theorem encode_length (message : BookStatusMessage) : (encode message).length = 22 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length]

theorem encode_length_pos (message : BookStatusMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : BookStatusMessage) (rest : List UInt8) :
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

end BookStatusMessage

/-- Book Entry Message: 18 bytes -/
structure BookEntryMessage where
  securityId : BitVec 16
  quantity : BitVec 32
  price : BitVec 64
  orderRef : BitVec 32
  deriving DecidableEq, Repr

namespace BookEntryMessage

def encode (message : BookEntryMessage) : List UInt8 :=
  encodeUIntLE 2 message.securityId
    ++ (encodeUIntLE 4 message.quantity
    ++ (encodeUIntLE 8 message.price
    ++ (encodeUIntLE 4 message.orderRef)))

def decode (bytes : List UInt8) : Option (BookEntryMessage × List UInt8) := do
  let (securityId, bytes) ← decodeUIntLE 2 bytes
  let (quantity, bytes) ← decodeUIntLE 4 bytes
  let (price, bytes) ← decodeUIntLE 8 bytes
  let (orderRef, bytes) ← decodeUIntLE 4 bytes
  pure ({ securityId, quantity, price, orderRef }, bytes)

@[simp] theorem encode_length (message : BookEntryMessage) : (encode message).length = 18 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length]

theorem encode_length_pos (message : BookEntryMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : BookEntryMessage) (rest : List UInt8) :
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

end BookEntryMessage

/-- Market At Close Book Entry Message: 18 bytes -/
structure MarketAtCloseBookEntryMessage where
  securityId : BitVec 16
  quantity : BitVec 32
  price : BitVec 64
  orderRef : BitVec 32
  deriving DecidableEq, Repr

namespace MarketAtCloseBookEntryMessage

def encode (message : MarketAtCloseBookEntryMessage) : List UInt8 :=
  encodeUIntLE 2 message.securityId
    ++ (encodeUIntLE 4 message.quantity
    ++ (encodeUIntLE 8 message.price
    ++ (encodeUIntLE 4 message.orderRef)))

def decode (bytes : List UInt8) : Option (MarketAtCloseBookEntryMessage × List UInt8) := do
  let (securityId, bytes) ← decodeUIntLE 2 bytes
  let (quantity, bytes) ← decodeUIntLE 4 bytes
  let (price, bytes) ← decodeUIntLE 8 bytes
  let (orderRef, bytes) ← decodeUIntLE 4 bytes
  pure ({ securityId, quantity, price, orderRef }, bytes)

@[simp] theorem encode_length (message : MarketAtCloseBookEntryMessage) : (encode message).length = 18 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length]

theorem encode_length_pos (message : MarketAtCloseBookEntryMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : MarketAtCloseBookEntryMessage) (rest : List UInt8) :
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

end MarketAtCloseBookEntryMessage

/-- Any Payload, selected by Msg Type -/
inductive Payload where
  | heartbeatMessage (message : HeartbeatMessage) -- 1
  | snapshotStartMessage (message : SnapshotStartMessage) -- 10
  | bookStatusMessage (message : BookStatusMessage) -- 11
  | bookEntryMessage (message : BookEntryMessage) -- 12
  | marketAtCloseBookEntryMessage (message : MarketAtCloseBookEntryMessage) -- 18
  deriving DecidableEq, Repr

namespace Payload

/-- The Msg Type each message is sent under -/
def tag : Payload → BitVec 8
  | .heartbeatMessage _ => 1
  | .snapshotStartMessage _ => 10
  | .bookStatusMessage _ => 11
  | .bookEntryMessage _ => 12
  | .marketAtCloseBookEntryMessage _ => 18

def encode : Payload → List UInt8
  | .heartbeatMessage message => HeartbeatMessage.encode message
  | .snapshotStartMessage message => SnapshotStartMessage.encode message
  | .bookStatusMessage message => BookStatusMessage.encode message
  | .bookEntryMessage message => BookEntryMessage.encode message
  | .marketAtCloseBookEntryMessage message => MarketAtCloseBookEntryMessage.encode message

def decode (tag : BitVec 8) (bytes : List UInt8) : Option (Payload × List UInt8) :=
  if tag = 1 then (HeartbeatMessage.decode bytes).map fun (message, rest) => (.heartbeatMessage message, rest)
  else if tag = 10 then (SnapshotStartMessage.decode bytes).map fun (message, rest) => (.snapshotStartMessage message, rest)
  else if tag = 11 then (BookStatusMessage.decode bytes).map fun (message, rest) => (.bookStatusMessage message, rest)
  else if tag = 12 then (BookEntryMessage.decode bytes).map fun (message, rest) => (.bookEntryMessage message, rest)
  else if tag = 18 then (MarketAtCloseBookEntryMessage.decode bytes).map fun (message, rest) => (.marketAtCloseBookEntryMessage message, rest)
  else none

@[simp] theorem decode_encode (message : Payload) (rest : List UInt8) :
    decode (tag message) (encode message ++ rest) = some (message, rest) := by
  cases message <;> simp [decode, encode, tag]

end Payload

/-- Message -/
structure Message where
  seqNo : BitVec 32
  payload : Payload
  deriving DecidableEq, Repr

namespace Message

def encodeBody (message : Message) : List UInt8 :=
  encodeUInt 4 message.seqNo
    ++ (Payload.encode message.payload)

def decodeBody (msgType : BitVec 8) (bytes : List UInt8) : Option (Message × List UInt8) := do
  let (seqNo, bytes) ← decodeUInt 4 bytes
  let (payload, bytes) ← Payload.decode msgType bytes
  pure ({ seqNo, payload }, bytes)

theorem decodeBody_encodeBody (message : Message) (rest : List UInt8) :
    decodeBody (Payload.tag message.payload) (encodeBody message ++ rest) = some (message, rest) := by
  unfold decodeBody encodeBody
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [Payload.decode_encode, some_bind]
  rfl

/-- Every body fits the length prefix -/
theorem encodeBody_length_lt (message : Message) : (encodeBody message).length + 2 < 256 ^ 1 := by
  unfold encodeBody
  cases message.payload with
  | heartbeatMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, HeartbeatMessage.encode_length]
    omega
  | snapshotStartMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, SnapshotStartMessage.encode_length]
    omega
  | bookStatusMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, BookStatusMessage.encode_length]
    omega
  | bookEntryMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, BookEntryMessage.encode_length]
    omega
  | marketAtCloseBookEntryMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, MarketAtCloseBookEntryMessage.encode_length]
    omega

/-- Size rule: Msg Length counts the bytes after it plus 2, so it is written from the body and checked on decode; Msg Type is read ahead of it -/
def encode (message : Message) : List UInt8 :=
  encodeUInt 1 (Payload.tag message.payload)
    ++ (encodeFramed 1 2 encodeBody message)

def decode (bytes : List UInt8) : Option (Message × List UInt8) := do
  let (msgType, bytes) ← decodeUInt 1 bytes
  decodeFramed 1 2 (decodeBody msgType) bytes

@[simp] theorem decode_encode (message : Message) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  exact decodeFramed_encodeFramed 1 2 encodeBody (decodeBody (Payload.tag message.payload)) message (decodeBody_encodeBody message) (encodeBody_length_lt message) rest

theorem encode_length_pos (message : Message) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUInt_length, List.length_append, encodeFramed_length]
  omega

end Message

/-- Packet -/
structure Packet where
  message : Bounded 1 Message
  deriving DecidableEq, Repr

namespace Packet

def encode (message : Packet) : List UInt8 :=
  encodeUInt 1 (BitVec.ofNat (8 * 1) message.message.val.length)
    ++ (encodeMany Message.encode message.message.val)

def decode (bytes : List UInt8) : Option (Packet × List UInt8) := do
  let (messageCount, bytes) ← decodeUInt 1 bytes
  let (message_, bytes) ← decodeMany Message.decode messageCount.toNat bytes
  if fits_message : message_.length < 256 ^ 1 then
    pure ({ message := ⟨message_, fits_message⟩ }, bytes)
  else none

theorem encode_length_pos (message : Packet) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUInt_length, List.length_append]
  omega

@[simp] theorem decode_encode (message : Packet) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeMany_bounded 1 Message.encode Message.decode Message.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.message.length_lt]
  rfl

end Packet

end Omi.A2xA2xequitiesSnapshotAmdV132
