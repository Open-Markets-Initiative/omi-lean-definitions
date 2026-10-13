import Wire

/-!
# The London Metal Exchange LMEsource WarehouseStock v4.18

Generated from the binary model, with the proofs the model's rules call for: every record
decodes back to what was encoded; a message dispatch selects the message its type names;
a count is written from the list it counts; a length prefix is written from the bytes it frames;
and a packet read to the end of its data decodes to the messages that were written.

Text fields are kept byte for byte, padding included, so what is decoded encodes back unchanged.
Prices with implied decimals are proven as the integers on the wire.
-/

namespace Omi.LmeLmeselectWarehousestockLmesourceV418

/-- Sequence Reset Message: 4 bytes -/
structure SequenceResetMessage where
  newSeqNo : BitVec 32
  deriving DecidableEq, Repr

namespace SequenceResetMessage

def encode (message : SequenceResetMessage) : List UInt8 :=
  encodeUIntLE 4 message.newSeqNo

def decode (bytes : List UInt8) : Option (SequenceResetMessage × List UInt8) := do
  let (newSeqNo, bytes) ← decodeUIntLE 4 bytes
  pure ({ newSeqNo }, bytes)

@[simp] theorem encode_length (message : SequenceResetMessage) : (encode message).length = 4 := by
  unfold encode
  simp only [encodeUIntLE_length]

theorem encode_length_pos (message : SequenceResetMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SequenceResetMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end SequenceResetMessage

/-- Stock Records: 17 bytes -/
structure StockRecords where
  productCode : Alpha 2
  location : Alpha 4
  gradeCode : Alpha 4
  stockStatus : Alpha 3
  stockQuantity : BitVec 32
  deriving DecidableEq, Repr

namespace StockRecords

def encode (message : StockRecords) : List UInt8 :=
  Alpha.encode message.productCode
    ++ (Alpha.encode message.location
    ++ (Alpha.encode message.gradeCode
    ++ (Alpha.encode message.stockStatus
    ++ (encodeUIntLE 4 message.stockQuantity))))

def decode (bytes : List UInt8) : Option (StockRecords × List UInt8) := do
  let (productCode, bytes) ← Alpha.decode 2 bytes
  let (location, bytes) ← Alpha.decode 4 bytes
  let (gradeCode, bytes) ← Alpha.decode 4 bytes
  let (stockStatus, bytes) ← Alpha.decode 3 bytes
  let (stockQuantity, bytes) ← decodeUIntLE 4 bytes
  pure ({ productCode, location, gradeCode, stockStatus, stockQuantity }, bytes)

@[simp] theorem encode_length (message : StockRecords) : (encode message).length = 17 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUIntLE_length]

theorem encode_length_pos (message : StockRecords) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : StockRecords) (rest : List UInt8) :
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
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end StockRecords

/-- Warehouse Stock Movement Message -/
structure WarehouseStockMovementMessage where
  reportDate : BitVec 32
  reportLevel : Alpha 12
  remainingRecords : BitVec 16
  stockRecords : Bounded 2 StockRecords
  deriving DecidableEq, Repr

namespace WarehouseStockMovementMessage

def encode (message : WarehouseStockMovementMessage) : List UInt8 :=
  encodeUIntLE 4 message.reportDate
    ++ (Alpha.encode message.reportLevel
    ++ (encodeUIntLE 2 message.remainingRecords
    ++ (encodeUIntLE 2 (BitVec.ofNat (8 * 2) message.stockRecords.val.length)
    ++ (encodeMany StockRecords.encode message.stockRecords.val))))

def decode (bytes : List UInt8) : Option (WarehouseStockMovementMessage × List UInt8) := do
  let (reportDate, bytes) ← decodeUIntLE 4 bytes
  let (reportLevel, bytes) ← Alpha.decode 12 bytes
  let (remainingRecords, bytes) ← decodeUIntLE 2 bytes
  let (recordCount, bytes) ← decodeUIntLE 2 bytes
  let (stockRecords_, bytes) ← decodeMany StockRecords.decode recordCount.toNat bytes
  if fits_stockRecords : stockRecords_.length < 256 ^ 2 then
    pure ({ reportDate, reportLevel, remainingRecords, stockRecords := ⟨stockRecords_, fits_stockRecords⟩ }, bytes)
  else none

theorem encode_length_pos (message : WarehouseStockMovementMessage) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUIntLE_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : WarehouseStockMovementMessage) : (encode message).length ≤ 1114115 := by
  have bound_stockRecords := message.stockRecords.length_lt
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, encodeUIntLE_length, Alpha.encode_length, encodeMany_length_const StockRecords.encode 17 StockRecords.encode_length]
  omega

@[simp] theorem decode_encode (message : WarehouseStockMovementMessage) (rest : List UInt8) :
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
  rw [decodeMany_bounded 2 StockRecords.encode StockRecords.decode StockRecords.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.stockRecords.length_lt]
  rfl

end WarehouseStockMovementMessage

/-- Any Payload, selected by Msg Type -/
inductive Payload where
  | sequenceResetMessage (message : SequenceResetMessage) -- 100
  | warehouseStockMovementMessage (message : WarehouseStockMovementMessage) -- 426
  deriving DecidableEq, Repr

namespace Payload

/-- The Msg Type each message is sent under -/
def tag : Payload → BitVec 16
  | .sequenceResetMessage _ => 100
  | .warehouseStockMovementMessage _ => 426

def encode : Payload → List UInt8
  | .sequenceResetMessage message => SequenceResetMessage.encode message
  | .warehouseStockMovementMessage message => WarehouseStockMovementMessage.encode message

/-- The most bytes any message's encoding can take -/
theorem encode_length_le (message : Payload) : (encode message).length ≤ 1114115 := by
  cases message with
  | sequenceResetMessage inner =>
    simp only [encode, SequenceResetMessage.encode_length]
    omega
  | warehouseStockMovementMessage inner =>
    have bound_inner := WarehouseStockMovementMessage.encode_length_le inner
    simp only [encode]
    omega

def decode (tag : BitVec 16) (bytes : List UInt8) : Option (Payload × List UInt8) :=
  if tag = 100 then (SequenceResetMessage.decode bytes).map fun (message, rest) => (.sequenceResetMessage message, rest)
  else if tag = 426 then (WarehouseStockMovementMessage.decode bytes).map fun (message, rest) => (.warehouseStockMovementMessage message, rest)
  else none

@[simp] theorem decode_encode (message : Payload) (rest : List UInt8) :
    decode (tag message) (encode message ++ rest) = some (message, rest) := by
  cases message <;> simp [decode, encode, tag]

end Payload

/-- Messages -/
structure Messages where
  msgSize : BitVec 16
  payload : Payload
  deriving DecidableEq, Repr

namespace Messages

def encode (message : Messages) : List UInt8 :=
  encodeUIntLE 2 message.msgSize
    ++ (encodeUIntLE 2 (Payload.tag message.payload)
    ++ (Payload.encode message.payload))

def decode (bytes : List UInt8) : Option (Messages × List UInt8) := do
  let (msgSize, bytes) ← decodeUIntLE 2 bytes
  let (msgType, bytes) ← decodeUIntLE 2 bytes
  let (payload, bytes) ← Payload.decode msgType bytes
  pure ({ msgSize, payload }, bytes)

theorem encode_length_pos (message : Messages) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUIntLE_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : Messages) : (encode message).length ≤ 1114119 := by
  unfold encode
  cases message.payload with
  | sequenceResetMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, SequenceResetMessage.encode_length]
    omega
  | warehouseStockMovementMessage inner =>
    have bound_inner := WarehouseStockMovementMessage.encode_length_le inner
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length]
    omega

@[simp] theorem decode_encode (message : Messages) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [Payload.decode_encode, some_bind]
  rfl

end Messages

/-- Packet -/
structure Packet where
  pktSize : BitVec 16
  filler : Alpha 1
  seqNum : BitVec 32
  sendTime : BitVec 64
  messages : Bounded 1 Messages
  deriving DecidableEq, Repr

namespace Packet

def encode (message : Packet) : List UInt8 :=
  encodeUIntLE 2 message.pktSize
    ++ (encodeUInt 1 (BitVec.ofNat (8 * 1) message.messages.val.length)
    ++ (Alpha.encode message.filler
    ++ (encodeUIntLE 4 message.seqNum
    ++ (encodeUIntLE 8 message.sendTime
    ++ (encodeMany Messages.encode message.messages.val)))))

def decode (bytes : List UInt8) : Option (Packet × List UInt8) := do
  let (pktSize, bytes) ← decodeUIntLE 2 bytes
  let (msgCount, bytes) ← decodeUInt 1 bytes
  let (filler, bytes) ← Alpha.decode 1 bytes
  let (seqNum, bytes) ← decodeUIntLE 4 bytes
  let (sendTime, bytes) ← decodeUIntLE 8 bytes
  let (messages_, bytes) ← decodeMany Messages.decode msgCount.toNat bytes
  if fits_messages : messages_.length < 256 ^ 1 then
    pure ({ pktSize, filler, seqNum, sendTime, messages := ⟨messages_, fits_messages⟩ }, bytes)
  else none

theorem encode_length_pos (message : Packet) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUIntLE_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : Packet) : (encode message).length ≤ 284100361 := by
  have bound_messages := message.messages.length_lt
  have bound_messages_items := encodeMany_length_le Messages.encode 1114119 Messages.encode_length_le message.messages.val
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, encodeUIntLE_length, encodeUInt_length, Alpha.encode_length]
  omega

@[simp] theorem decode_encode (message : Packet) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeMany_bounded 1 Messages.encode Messages.decode Messages.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.messages.length_lt]
  rfl

end Packet

end Omi.LmeLmeselectWarehousestockLmesourceV418
