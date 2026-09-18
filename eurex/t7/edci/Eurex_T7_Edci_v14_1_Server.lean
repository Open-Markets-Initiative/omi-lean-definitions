import Omi.Wire

/-!
# Eurex Exchange Extended Derivatives Clearing Interface v14.1

Generated from the binary model, with the proofs the model's rules call for: every record
decodes back to what was encoded; a message dispatch selects the message its type names;
a count is written from the list it counts; a length prefix is written from the bytes it frames;
and a packet read to the end of its data decodes to the messages that were written.

Note: Delete Order Broadcast is not framed: its length Body Len is not an integer it reads.

Note: Alignment Padding pads to a 8 byte boundary: it is read as the bytes left to the end of the frame, fewer than 8, and the frame's length is trusted to keep the boundary.

Note: Forced Logout Notification is not framed: its length Body Len is not an integer it reads.

Note: Heartbeat Notification is not framed: its length Body Len is not an integer it reads.

Note: Logon Response is not framed: its length Body Len is not an integer it reads.

Note: Logout Response is not framed: its length Body Len is not an integer it reads.

Note: Order Exec Report Broadcast is not framed: its length Body Len is not an integer it reads.

Note: Partition List Notification is not framed: its length Body Len is not an integer it reads.

Note: Alignment Padding pads to a 8 byte boundary: it is read as the bytes left to the end of the frame, fewer than 8, and the frame's length is trusted to keep the boundary.

Note: Reject is not framed: its length Body Len is not an integer it reads.

Note: Session List Notification is not framed: its length Body Len is not an integer it reads.

Note: Session Status Broadcast is not framed: its length Body Len is not an integer it reads.

Text fields are kept byte for byte, padding included, so what is decoded encodes back unchanged.
Prices with implied decimals are proven as the integers on the wire.
-/

namespace Omi.EurexT7EdciFbeV141Server

/-- Ord Status: one byte code -/
def OrdStatus.codes : List UInt8 :=
  [0x30, 0x31, 0x32, 0x34, 0x36, 0x39]

inductive OrdStatus where
  | new -- New
  | partiallyfilled -- Partiallyfilled
  | filled -- Filled
  | canceled -- Canceled
  | pendingCancel -- Pending Cancel
  | suspended -- Suspended
  | unlisted (byte : { byte : UInt8 // byte ∉ OrdStatus.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace OrdStatus

def toByte : OrdStatus → UInt8
  | .new => 0x30
  | .partiallyfilled => 0x31
  | .filled => 0x32
  | .canceled => 0x34
  | .pendingCancel => 0x36
  | .suspended => 0x39
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : OrdStatus :=
  if byte = 0x30 then .new
  else if byte = 0x31 then .partiallyfilled
  else if byte = 0x32 then .filled
  else if byte = 0x34 then .canceled
  else if byte = 0x36 then .pendingCancel
  else .suspended

def ofByte (byte : UInt8) : OrdStatus :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : OrdStatus) : ofByte value.toByte = value := by
  cases value with
  | new => decide
  | partiallyfilled => decide
  | filled => decide
  | canceled => decide
  | pendingCancel => decide
  | suspended => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : OrdStatus) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (OrdStatus × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : OrdStatus) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : OrdStatus) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end OrdStatus

/-- Exec Type: one byte code -/
def ExecType.codes : List UInt8 :=
  [0x30, 0x34, 0x35, 0x36, 0x39, 0x44, 0x4C, 0x46]

inductive ExecType where
  | new -- New
  | canceled -- Canceled
  | replaced -- Replaced
  | pendingCancele -- Pending Cancele
  | suspended -- Suspended
  | restated -- Restated
  | triggered -- Triggered
  | trade -- Trade
  | unlisted (byte : { byte : UInt8 // byte ∉ ExecType.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace ExecType

def toByte : ExecType → UInt8
  | .new => 0x30
  | .canceled => 0x34
  | .replaced => 0x35
  | .pendingCancele => 0x36
  | .suspended => 0x39
  | .restated => 0x44
  | .triggered => 0x4C
  | .trade => 0x46
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : ExecType :=
  if byte = 0x30 then .new
  else if byte = 0x34 then .canceled
  else if byte = 0x35 then .replaced
  else if byte = 0x36 then .pendingCancele
  else if byte = 0x39 then .suspended
  else if byte = 0x44 then .restated
  else if byte = 0x4C then .triggered
  else .trade

def ofByte (byte : UInt8) : ExecType :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : ExecType) : ofByte value.toByte = value := by
  cases value with
  | new => decide
  | canceled => decide
  | replaced => decide
  | pendingCancele => decide
  | suspended => decide
  | restated => decide
  | triggered => decide
  | trade => decide
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

/-- Cust Order Handling Inst: one byte code -/
def CustOrderHandlingInst.codes : List UInt8 :=
  [0x57, 0x59, 0x43, 0x47, 0x48, 0x44]

inductive CustOrderHandlingInst where
  | w -- W
  | y -- Y
  | c -- C
  | g -- G
  | h -- H
  | d -- D
  | unlisted (byte : { byte : UInt8 // byte ∉ CustOrderHandlingInst.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace CustOrderHandlingInst

def toByte : CustOrderHandlingInst → UInt8
  | .w => 0x57
  | .y => 0x59
  | .c => 0x43
  | .g => 0x47
  | .h => 0x48
  | .d => 0x44
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : CustOrderHandlingInst :=
  if byte = 0x57 then .w
  else if byte = 0x59 then .y
  else if byte = 0x43 then .c
  else if byte = 0x47 then .g
  else if byte = 0x48 then .h
  else .d

def ofByte (byte : UInt8) : CustOrderHandlingInst :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : CustOrderHandlingInst) : ofByte value.toByte = value := by
  cases value with
  | w => decide
  | y => decide
  | c => decide
  | g => decide
  | h => decide
  | d => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : CustOrderHandlingInst) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (CustOrderHandlingInst × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : CustOrderHandlingInst) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : CustOrderHandlingInst) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end CustOrderHandlingInst

/-- Rbc Header Comp: 16 bytes -/
structure RbcHeaderComp where
  sendingTime : BitVec 64
  partyIdExecutingUnit : BitVec 32
  partitionId : BitVec 16
  applId : BitVec 8
  lastFragment : BitVec 8
  deriving DecidableEq, Repr

namespace RbcHeaderComp

def encode (message : RbcHeaderComp) : List UInt8 :=
  encodeUIntLE 8 message.sendingTime
    ++ (encodeUIntLE 4 message.partyIdExecutingUnit
    ++ (encodeUIntLE 2 message.partitionId
    ++ (encodeUInt 1 message.applId
    ++ (encodeUInt 1 message.lastFragment))))

def decode (bytes : List UInt8) : Option (RbcHeaderComp × List UInt8) := do
  let (sendingTime, bytes) ← decodeUIntLE 8 bytes
  let (partyIdExecutingUnit, bytes) ← decodeUIntLE 4 bytes
  let (partitionId, bytes) ← decodeUIntLE 2 bytes
  let (applId, bytes) ← decodeUInt 1 bytes
  let (lastFragment, bytes) ← decodeUInt 1 bytes
  pure ({ sendingTime, partyIdExecutingUnit, partitionId, applId, lastFragment }, bytes)

@[simp] theorem encode_length (message : RbcHeaderComp) : (encode message).length = 16 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, encodeUInt_length]

theorem encode_length_pos (message : RbcHeaderComp) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : RbcHeaderComp) (rest : List UInt8) :
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

end RbcHeaderComp

/-- Affected Ord Grp Comp: 88 bytes -/
structure AffectedOrdGrpComp where
  affectedOrderId : BitVec 64
  affectedClOrdId : BitVec 64
  affectedOrigClOrdId : BitVec 64
  securityId : BitVec 64
  partyIdSessionId : BitVec 32
  partyIdExecutingTrader : BitVec 32
  ordStatus : OrdStatus
  execType : ExecType
  affectedFixClOrdId : Alpha 20
  affectedFixOrigClOrdId : Alpha 20
  pad6 : Alpha 6
  deriving DecidableEq, Repr

namespace AffectedOrdGrpComp

def encode (message : AffectedOrdGrpComp) : List UInt8 :=
  encodeUIntLE 8 message.affectedOrderId
    ++ (encodeUIntLE 8 message.affectedClOrdId
    ++ (encodeUIntLE 8 message.affectedOrigClOrdId
    ++ (encodeUIntLE 8 message.securityId
    ++ (encodeUIntLE 4 message.partyIdSessionId
    ++ (encodeUIntLE 4 message.partyIdExecutingTrader
    ++ (OrdStatus.encode message.ordStatus
    ++ (ExecType.encode message.execType
    ++ (Alpha.encode message.affectedFixClOrdId
    ++ (Alpha.encode message.affectedFixOrigClOrdId
    ++ (Alpha.encode message.pad6))))))))))

def decode (bytes : List UInt8) : Option (AffectedOrdGrpComp × List UInt8) := do
  let (affectedOrderId, bytes) ← decodeUIntLE 8 bytes
  let (affectedClOrdId, bytes) ← decodeUIntLE 8 bytes
  let (affectedOrigClOrdId, bytes) ← decodeUIntLE 8 bytes
  let (securityId, bytes) ← decodeUIntLE 8 bytes
  let (partyIdSessionId, bytes) ← decodeUIntLE 4 bytes
  let (partyIdExecutingTrader, bytes) ← decodeUIntLE 4 bytes
  let (ordStatus, bytes) ← OrdStatus.decode bytes
  let (execType, bytes) ← ExecType.decode bytes
  let (affectedFixClOrdId, bytes) ← Alpha.decode 20 bytes
  let (affectedFixOrigClOrdId, bytes) ← Alpha.decode 20 bytes
  let (pad6, bytes) ← Alpha.decode 6 bytes
  pure ({ affectedOrderId, affectedClOrdId, affectedOrigClOrdId, securityId, partyIdSessionId, partyIdExecutingTrader, ordStatus, execType, affectedFixClOrdId, affectedFixOrigClOrdId, pad6 }, bytes)

@[simp] theorem encode_length (message : AffectedOrdGrpComp) : (encode message).length = 88 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, OrdStatus.encode_length, ExecType.encode_length, Alpha.encode_length]

theorem encode_length_pos (message : AffectedOrdGrpComp) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : AffectedOrdGrpComp) (rest : List UInt8) :
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
  rw [List.append_assoc, OrdStatus.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, ExecType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end AffectedOrdGrpComp

/-- Delete Order Broadcast -/
structure DeleteOrderBroadcast where
  pad2 : Alpha 2
  rbcHeaderComp : RbcHeaderComp
  execId : BitVec 64
  marketSegmentId : BitVec 32
  pad2v2 : Alpha 2
  affectedOrdGrpComp : Bounded 2 AffectedOrdGrpComp
  deriving DecidableEq, Repr

namespace DeleteOrderBroadcast

def encode (message : DeleteOrderBroadcast) : List UInt8 :=
  Alpha.encode message.pad2
    ++ (RbcHeaderComp.encode message.rbcHeaderComp
    ++ (encodeUIntLE 8 message.execId
    ++ (encodeUIntLE 4 message.marketSegmentId
    ++ (encodeUIntLE 2 (BitVec.ofNat (8 * 2) message.affectedOrdGrpComp.val.length)
    ++ (Alpha.encode message.pad2v2
    ++ (encodeMany AffectedOrdGrpComp.encode message.affectedOrdGrpComp.val))))))

def decode (bytes : List UInt8) : Option (DeleteOrderBroadcast × List UInt8) := do
  let (pad2, bytes) ← Alpha.decode 2 bytes
  let (rbcHeaderComp, bytes) ← RbcHeaderComp.decode bytes
  let (execId, bytes) ← decodeUIntLE 8 bytes
  let (marketSegmentId, bytes) ← decodeUIntLE 4 bytes
  let (noAffectedOrders, bytes) ← decodeUIntLE 2 bytes
  let (pad2v2, bytes) ← Alpha.decode 2 bytes
  let (affectedOrdGrpComp_, bytes) ← decodeMany AffectedOrdGrpComp.decode noAffectedOrders.toNat bytes
  if fits_affectedOrdGrpComp : affectedOrdGrpComp_.length < 256 ^ 2 then
    pure ({ pad2, rbcHeaderComp, execId, marketSegmentId, pad2v2, affectedOrdGrpComp := ⟨affectedOrdGrpComp_, fits_affectedOrdGrpComp⟩ }, bytes)
  else none

theorem encode_length_pos (message : DeleteOrderBroadcast) : (encode message).length > 0 := by
  unfold encode
  simp only [Alpha.encode_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : DeleteOrderBroadcast) : (encode message).length ≤ 5767114 := by
  have bound_affectedOrdGrpComp := message.affectedOrdGrpComp.length_lt
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, Alpha.encode_length, RbcHeaderComp.encode_length, encodeUIntLE_length, encodeMany_length_const AffectedOrdGrpComp.encode 88 AffectedOrdGrpComp.encode_length]
  omega

@[simp] theorem decode_encode (message : DeleteOrderBroadcast) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, RbcHeaderComp.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [decodeMany_bounded 2 AffectedOrdGrpComp.encode AffectedOrdGrpComp.decode AffectedOrdGrpComp.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.affectedOrdGrpComp.length_lt]
  rfl

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : DeleteOrderBroadcast) : decode (encode message) = some (message, []) :=
  List.append_nil (encode message) ▸ decode_encode message []

end DeleteOrderBroadcast

/-- Notif Header Comp: 8 bytes -/
structure NotifHeaderComp where
  sendingTime : BitVec 64
  deriving DecidableEq, Repr

namespace NotifHeaderComp

def encode (message : NotifHeaderComp) : List UInt8 :=
  encodeUIntLE 8 message.sendingTime

def decode (bytes : List UInt8) : Option (NotifHeaderComp × List UInt8) := do
  let (sendingTime, bytes) ← decodeUIntLE 8 bytes
  pure ({ sendingTime }, bytes)

@[simp] theorem encode_length (message : NotifHeaderComp) : (encode message).length = 8 := by
  unfold encode
  simp only [encodeUIntLE_length]

theorem encode_length_pos (message : NotifHeaderComp) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : NotifHeaderComp) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end NotifHeaderComp

/-- Forced Logout Notification -/
structure ForcedLogoutNotification where
  pad2 : Alpha 2
  notifHeaderComp : NotifHeaderComp
  varText : Bounded 2 UInt8
  alignmentPadding : Capped 7
  deriving DecidableEq, Repr

namespace ForcedLogoutNotification

def encode (message : ForcedLogoutNotification) : List UInt8 :=
  Alpha.encode message.pad2
    ++ (NotifHeaderComp.encode message.notifHeaderComp
    ++ (encodeUIntLE 2 (BitVec.ofNat (8 * 2) message.varText.val.length)
    ++ (encodeMany Byte.encode message.varText.val
    ++ (message.alignmentPadding.val))))

def decode (bytes : List UInt8) : Option ForcedLogoutNotification := do
  let (pad2, bytes) ← Alpha.decode 2 bytes
  let (notifHeaderComp, bytes) ← NotifHeaderComp.decode bytes
  let (varTextLen, bytes) ← decodeUIntLE 2 bytes
  let (varText_, bytes) ← decodeMany Byte.decode varTextLen.toNat bytes
  let alignmentPadding_ := bytes
  if fits_varText : varText_.length < 256 ^ 2 then
    if fits_alignmentPadding : alignmentPadding_.length ≤ 7 then
      pure { pad2, notifHeaderComp, varText := ⟨varText_, fits_varText⟩, alignmentPadding := ⟨alignmentPadding_, fits_alignmentPadding⟩ }
    else none
  else none

theorem encode_length_pos (message : ForcedLogoutNotification) : (encode message).length > 0 := by
  unfold encode
  simp only [Alpha.encode_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : ForcedLogoutNotification) : (encode message).length ≤ 65554 := by
  have bound_varText := message.varText.length_lt
  have bound_alignmentPadding := message.alignmentPadding.length_le
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, Alpha.encode_length, NotifHeaderComp.encode_length, encodeUIntLE_length, encodeMany_length_const Byte.encode 1 Byte.encode_length]
  omega

theorem decode_encode (message : ForcedLogoutNotification) : decode (encode message) = some message := by
  unfold decode encode
  rw [Alpha.decode_encode, some_bind]
  dsimp only
  rw [NotifHeaderComp.decode_encode, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeMany_bounded 2 Byte.encode Byte.decode Byte.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.varText.length_lt, dite_eq_left message.alignmentPadding.length_le]
  rfl

end ForcedLogoutNotification

/-- Heartbeat Notification: 10 bytes -/
structure HeartbeatNotification where
  pad2 : Alpha 2
  notifHeaderComp : NotifHeaderComp
  deriving DecidableEq, Repr

namespace HeartbeatNotification

def encode (message : HeartbeatNotification) : List UInt8 :=
  Alpha.encode message.pad2
    ++ (NotifHeaderComp.encode message.notifHeaderComp)

def decode (bytes : List UInt8) : Option (HeartbeatNotification × List UInt8) := do
  let (pad2, bytes) ← Alpha.decode 2 bytes
  let (notifHeaderComp, bytes) ← NotifHeaderComp.decode bytes
  pure ({ pad2, notifHeaderComp }, bytes)

@[simp] theorem encode_length (message : HeartbeatNotification) : (encode message).length = 10 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, NotifHeaderComp.encode_length]

theorem encode_length_pos (message : HeartbeatNotification) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : HeartbeatNotification) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [NotifHeaderComp.decode_encode, some_bind]
  rfl

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : HeartbeatNotification) : decode (encode message) = some (message, []) :=
  List.append_nil (encode message) ▸ decode_encode message []

end HeartbeatNotification

/-- Response Header Comp: 24 bytes -/
structure ResponseHeaderComp where
  requestTime : BitVec 64
  sendingTime : BitVec 64
  msgSeqNum : BitVec 32
  lastFragment : BitVec 8
  pad3 : Alpha 3
  deriving DecidableEq, Repr

namespace ResponseHeaderComp

def encode (message : ResponseHeaderComp) : List UInt8 :=
  encodeUIntLE 8 message.requestTime
    ++ (encodeUIntLE 8 message.sendingTime
    ++ (encodeUIntLE 4 message.msgSeqNum
    ++ (encodeUInt 1 message.lastFragment
    ++ (Alpha.encode message.pad3))))

def decode (bytes : List UInt8) : Option (ResponseHeaderComp × List UInt8) := do
  let (requestTime, bytes) ← decodeUIntLE 8 bytes
  let (sendingTime, bytes) ← decodeUIntLE 8 bytes
  let (msgSeqNum, bytes) ← decodeUIntLE 4 bytes
  let (lastFragment, bytes) ← decodeUInt 1 bytes
  let (pad3, bytes) ← Alpha.decode 3 bytes
  pure ({ requestTime, sendingTime, msgSeqNum, lastFragment, pad3 }, bytes)

@[simp] theorem encode_length (message : ResponseHeaderComp) : (encode message).length = 24 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, encodeUInt_length, Alpha.encode_length]

theorem encode_length_pos (message : ResponseHeaderComp) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : ResponseHeaderComp) (rest : List UInt8) :
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
  rw [Alpha.decode_encode, some_bind]
  rfl

end ResponseHeaderComp

/-- Logon Response: 74 bytes -/
structure LogonResponse where
  pad2 : Alpha 2
  responseHeaderComp : ResponseHeaderComp
  heartBtInt : BitVec 32
  sessionInstanceId : BitVec 32
  marketId : BitVec 16
  tradSesMode : BitVec 8
  defaultCstmApplVerId : Alpha 30
  defaultCstmApplVerSubId : Alpha 5
  pad2v2 : Alpha 2
  deriving DecidableEq, Repr

namespace LogonResponse

def encode (message : LogonResponse) : List UInt8 :=
  Alpha.encode message.pad2
    ++ (ResponseHeaderComp.encode message.responseHeaderComp
    ++ (encodeUIntLE 4 message.heartBtInt
    ++ (encodeUIntLE 4 message.sessionInstanceId
    ++ (encodeUIntLE 2 message.marketId
    ++ (encodeUInt 1 message.tradSesMode
    ++ (Alpha.encode message.defaultCstmApplVerId
    ++ (Alpha.encode message.defaultCstmApplVerSubId
    ++ (Alpha.encode message.pad2v2))))))))

def decode (bytes : List UInt8) : Option (LogonResponse × List UInt8) := do
  let (pad2, bytes) ← Alpha.decode 2 bytes
  let (responseHeaderComp, bytes) ← ResponseHeaderComp.decode bytes
  let (heartBtInt, bytes) ← decodeUIntLE 4 bytes
  let (sessionInstanceId, bytes) ← decodeUIntLE 4 bytes
  let (marketId, bytes) ← decodeUIntLE 2 bytes
  let (tradSesMode, bytes) ← decodeUInt 1 bytes
  let (defaultCstmApplVerId, bytes) ← Alpha.decode 30 bytes
  let (defaultCstmApplVerSubId, bytes) ← Alpha.decode 5 bytes
  let (pad2v2, bytes) ← Alpha.decode 2 bytes
  pure ({ pad2, responseHeaderComp, heartBtInt, sessionInstanceId, marketId, tradSesMode, defaultCstmApplVerId, defaultCstmApplVerSubId, pad2v2 }, bytes)

@[simp] theorem encode_length (message : LogonResponse) : (encode message).length = 74 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, ResponseHeaderComp.encode_length, encodeUIntLE_length, encodeUInt_length]

theorem encode_length_pos (message : LogonResponse) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : LogonResponse) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, ResponseHeaderComp.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : LogonResponse) : decode (encode message) = some (message, []) :=
  List.append_nil (encode message) ▸ decode_encode message []

end LogonResponse

/-- Logout Response: 26 bytes -/
structure LogoutResponse where
  pad2 : Alpha 2
  responseHeaderComp : ResponseHeaderComp
  deriving DecidableEq, Repr

namespace LogoutResponse

def encode (message : LogoutResponse) : List UInt8 :=
  Alpha.encode message.pad2
    ++ (ResponseHeaderComp.encode message.responseHeaderComp)

def decode (bytes : List UInt8) : Option (LogoutResponse × List UInt8) := do
  let (pad2, bytes) ← Alpha.decode 2 bytes
  let (responseHeaderComp, bytes) ← ResponseHeaderComp.decode bytes
  pure ({ pad2, responseHeaderComp }, bytes)

@[simp] theorem encode_length (message : LogoutResponse) : (encode message).length = 26 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, ResponseHeaderComp.encode_length]

theorem encode_length_pos (message : LogoutResponse) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : LogoutResponse) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [ResponseHeaderComp.decode_encode, some_bind]
  rfl

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : LogoutResponse) : decode (encode message) = some (message, []) :=
  List.append_nil (encode message) ▸ decode_encode message []

end LogoutResponse

/-- Fills Grp Comp: 24 bytes -/
structure FillsGrpComp where
  fillPx : BitVec 64
  fillQty : BitVec 64
  fillMatchId : BitVec 32
  fillExecId : BitVec 32
  deriving DecidableEq, Repr

namespace FillsGrpComp

def encode (message : FillsGrpComp) : List UInt8 :=
  encodeUIntLE 8 message.fillPx
    ++ (encodeUIntLE 8 message.fillQty
    ++ (encodeUIntLE 4 message.fillMatchId
    ++ (encodeUIntLE 4 message.fillExecId)))

def decode (bytes : List UInt8) : Option (FillsGrpComp × List UInt8) := do
  let (fillPx, bytes) ← decodeUIntLE 8 bytes
  let (fillQty, bytes) ← decodeUIntLE 8 bytes
  let (fillMatchId, bytes) ← decodeUIntLE 4 bytes
  let (fillExecId, bytes) ← decodeUIntLE 4 bytes
  pure ({ fillPx, fillQty, fillMatchId, fillExecId }, bytes)

@[simp] theorem encode_length (message : FillsGrpComp) : (encode message).length = 24 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length]

theorem encode_length_pos (message : FillsGrpComp) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : FillsGrpComp) (rest : List UInt8) :
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

end FillsGrpComp

/-- Order Exec Report Broadcast -/
structure OrderExecReportBroadcast where
  pad2 : Alpha 2
  rbcHeaderComp : RbcHeaderComp
  orderId : BitVec 64
  clOrdId : BitVec 64
  origClOrdId : BitVec 64
  securityId : BitVec 64
  execId : BitVec 64
  price : BitVec 64
  stopPx : BitVec 64
  leavesQty : BitVec 64
  cumQty : BitVec 64
  cxlQty : BitVec 64
  orderQty : BitVec 64
  partyIdClientId : BitVec 64
  partyIdInvestmentDecisionMaker : BitVec 64
  executingTrader : BitVec 64
  marketSegmentId : BitVec 32
  matchInstCrossId : BitVec 32
  expireDate : BitVec 32
  partyIdSessionId : BitVec 32
  partyIdExecutingTrader : BitVec 32
  productComplex : BitVec 8
  ordStatus : OrdStatus
  execType : ExecType
  side : BitVec 8
  ordType : BitVec 8
  matchType : BitVec 8
  tradingCapacity : BitVec 8
  timeInForce : BitVec 8
  execInst : BitVec 8
  triggered : BitVec 8
  tradingSessionSubId : BitVec 8
  applSeqIndicator : BitVec 8
  selfMatchPreventionInstruction : BitVec 8
  crossMatchInstruction : BitVec 8
  partyIdInvestmentDecisionMakerQualifier : BitVec 8
  executingTraderQualifier : BitVec 8
  crossedIndicator : BitVec 8
  custOrderHandlingInst : CustOrderHandlingInst
  orderOrigination : BitVec 8
  freeText1 : Alpha 12
  freeText2 : Alpha 12
  freeText3 : Alpha 12
  fixClOrdId : Alpha 20
  fixOrigClOrdId : Alpha 20
  partyEndClientIdentification : Alpha 20
  fillsGrpComp : Bounded 1 FillsGrpComp
  deriving DecidableEq, Repr

namespace OrderExecReportBroadcast

def encode (message : OrderExecReportBroadcast) : List UInt8 :=
  Alpha.encode message.pad2
    ++ (RbcHeaderComp.encode message.rbcHeaderComp
    ++ (encodeUIntLE 8 message.orderId
    ++ (encodeUIntLE 8 message.clOrdId
    ++ (encodeUIntLE 8 message.origClOrdId
    ++ (encodeUIntLE 8 message.securityId
    ++ (encodeUIntLE 8 message.execId
    ++ (encodeUIntLE 8 message.price
    ++ (encodeUIntLE 8 message.stopPx
    ++ (encodeUIntLE 8 message.leavesQty
    ++ (encodeUIntLE 8 message.cumQty
    ++ (encodeUIntLE 8 message.cxlQty
    ++ (encodeUIntLE 8 message.orderQty
    ++ (encodeUIntLE 8 message.partyIdClientId
    ++ (encodeUIntLE 8 message.partyIdInvestmentDecisionMaker
    ++ (encodeUIntLE 8 message.executingTrader
    ++ (encodeUIntLE 4 message.marketSegmentId
    ++ (encodeUIntLE 4 message.matchInstCrossId
    ++ (encodeUIntLE 4 message.expireDate
    ++ (encodeUIntLE 4 message.partyIdSessionId
    ++ (encodeUIntLE 4 message.partyIdExecutingTrader
    ++ (encodeUInt 1 message.productComplex
    ++ (OrdStatus.encode message.ordStatus
    ++ (ExecType.encode message.execType
    ++ (encodeUInt 1 message.side
    ++ (encodeUInt 1 message.ordType
    ++ (encodeUInt 1 message.matchType
    ++ (encodeUInt 1 message.tradingCapacity
    ++ (encodeUInt 1 message.timeInForce
    ++ (encodeUInt 1 message.execInst
    ++ (encodeUInt 1 message.triggered
    ++ (encodeUInt 1 message.tradingSessionSubId
    ++ (encodeUInt 1 message.applSeqIndicator
    ++ (encodeUInt 1 message.selfMatchPreventionInstruction
    ++ (encodeUInt 1 message.crossMatchInstruction
    ++ (encodeUInt 1 message.partyIdInvestmentDecisionMakerQualifier
    ++ (encodeUInt 1 message.executingTraderQualifier
    ++ (encodeUInt 1 (BitVec.ofNat (8 * 1) message.fillsGrpComp.val.length)
    ++ (encodeUInt 1 message.crossedIndicator
    ++ (CustOrderHandlingInst.encode message.custOrderHandlingInst
    ++ (encodeUInt 1 message.orderOrigination
    ++ (Alpha.encode message.freeText1
    ++ (Alpha.encode message.freeText2
    ++ (Alpha.encode message.freeText3
    ++ (Alpha.encode message.fixClOrdId
    ++ (Alpha.encode message.fixOrigClOrdId
    ++ (Alpha.encode message.partyEndClientIdentification
    ++ (encodeMany FillsGrpComp.encode message.fillsGrpComp.val)))))))))))))))))))))))))))))))))))))))))))))))

-- a long run of fields nests deeper than the elaborator's default limit
set_option maxRecDepth 4096 in
def decode (bytes : List UInt8) : Option (OrderExecReportBroadcast × List UInt8) := do
  let (pad2, bytes) ← Alpha.decode 2 bytes
  let (rbcHeaderComp, bytes) ← RbcHeaderComp.decode bytes
  let (orderId, bytes) ← decodeUIntLE 8 bytes
  let (clOrdId, bytes) ← decodeUIntLE 8 bytes
  let (origClOrdId, bytes) ← decodeUIntLE 8 bytes
  let (securityId, bytes) ← decodeUIntLE 8 bytes
  let (execId, bytes) ← decodeUIntLE 8 bytes
  let (price, bytes) ← decodeUIntLE 8 bytes
  let (stopPx, bytes) ← decodeUIntLE 8 bytes
  let (leavesQty, bytes) ← decodeUIntLE 8 bytes
  let (cumQty, bytes) ← decodeUIntLE 8 bytes
  let (cxlQty, bytes) ← decodeUIntLE 8 bytes
  let (orderQty, bytes) ← decodeUIntLE 8 bytes
  let (partyIdClientId, bytes) ← decodeUIntLE 8 bytes
  let (partyIdInvestmentDecisionMaker, bytes) ← decodeUIntLE 8 bytes
  let (executingTrader, bytes) ← decodeUIntLE 8 bytes
  let (marketSegmentId, bytes) ← decodeUIntLE 4 bytes
  let (matchInstCrossId, bytes) ← decodeUIntLE 4 bytes
  let (expireDate, bytes) ← decodeUIntLE 4 bytes
  let (partyIdSessionId, bytes) ← decodeUIntLE 4 bytes
  let (partyIdExecutingTrader, bytes) ← decodeUIntLE 4 bytes
  let (productComplex, bytes) ← decodeUInt 1 bytes
  let (ordStatus, bytes) ← OrdStatus.decode bytes
  let (execType, bytes) ← ExecType.decode bytes
  let (side, bytes) ← decodeUInt 1 bytes
  let (ordType, bytes) ← decodeUInt 1 bytes
  let (matchType, bytes) ← decodeUInt 1 bytes
  let (tradingCapacity, bytes) ← decodeUInt 1 bytes
  let (timeInForce, bytes) ← decodeUInt 1 bytes
  let (execInst, bytes) ← decodeUInt 1 bytes
  let (triggered, bytes) ← decodeUInt 1 bytes
  let (tradingSessionSubId, bytes) ← decodeUInt 1 bytes
  let (applSeqIndicator, bytes) ← decodeUInt 1 bytes
  let (selfMatchPreventionInstruction, bytes) ← decodeUInt 1 bytes
  let (crossMatchInstruction, bytes) ← decodeUInt 1 bytes
  let (partyIdInvestmentDecisionMakerQualifier, bytes) ← decodeUInt 1 bytes
  let (executingTraderQualifier, bytes) ← decodeUInt 1 bytes
  let (noFills, bytes) ← decodeUInt 1 bytes
  let (crossedIndicator, bytes) ← decodeUInt 1 bytes
  let (custOrderHandlingInst, bytes) ← CustOrderHandlingInst.decode bytes
  let (orderOrigination, bytes) ← decodeUInt 1 bytes
  let (freeText1, bytes) ← Alpha.decode 12 bytes
  let (freeText2, bytes) ← Alpha.decode 12 bytes
  let (freeText3, bytes) ← Alpha.decode 12 bytes
  let (fixClOrdId, bytes) ← Alpha.decode 20 bytes
  let (fixOrigClOrdId, bytes) ← Alpha.decode 20 bytes
  let (partyEndClientIdentification, bytes) ← Alpha.decode 20 bytes
  let (fillsGrpComp_, bytes) ← decodeMany FillsGrpComp.decode noFills.toNat bytes
  if fits_fillsGrpComp : fillsGrpComp_.length < 256 ^ 1 then
    pure ({ pad2, rbcHeaderComp, orderId, clOrdId, origClOrdId, securityId, execId, price, stopPx, leavesQty, cumQty, cxlQty, orderQty, partyIdClientId, partyIdInvestmentDecisionMaker, executingTrader, marketSegmentId, matchInstCrossId, expireDate, partyIdSessionId, partyIdExecutingTrader, productComplex, ordStatus, execType, side, ordType, matchType, tradingCapacity, timeInForce, execInst, triggered, tradingSessionSubId, applSeqIndicator, selfMatchPreventionInstruction, crossMatchInstruction, partyIdInvestmentDecisionMakerQualifier, executingTraderQualifier, crossedIndicator, custOrderHandlingInst, orderOrigination, freeText1, freeText2, freeText3, fixClOrdId, fixOrigClOrdId, partyEndClientIdentification, fillsGrpComp := ⟨fillsGrpComp_, fits_fillsGrpComp⟩ }, bytes)
  else none

theorem encode_length_pos (message : OrderExecReportBroadcast) : (encode message).length > 0 := by
  unfold encode
  simp only [Alpha.encode_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : OrderExecReportBroadcast) : (encode message).length ≤ 6386 := by
  have bound_fillsGrpComp := message.fillsGrpComp.length_lt
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, Alpha.encode_length, RbcHeaderComp.encode_length, encodeUIntLE_length, encodeUInt_length, OrdStatus.encode_length, ExecType.encode_length, CustOrderHandlingInst.encode_length, encodeMany_length_const FillsGrpComp.encode 24 FillsGrpComp.encode_length]
  omega

set_option maxRecDepth 4096 in
@[simp] theorem decode_encode (message : OrderExecReportBroadcast) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, RbcHeaderComp.decode_encode, some_bind]
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
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, OrdStatus.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, ExecType.decode_encode, some_bind]
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
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, CustOrderHandlingInst.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
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
  rw [decodeMany_bounded 1 FillsGrpComp.encode FillsGrpComp.decode FillsGrpComp.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.fillsGrpComp.length_lt]
  rfl

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : OrderExecReportBroadcast) : decode (encode message) = some (message, []) :=
  List.append_nil (encode message) ▸ decode_encode message []

end OrderExecReportBroadcast

/-- Partition Grp Comp: 8 bytes -/
structure PartitionGrpComp where
  partitionId : BitVec 16
  pad6 : Alpha 6
  deriving DecidableEq, Repr

namespace PartitionGrpComp

def encode (message : PartitionGrpComp) : List UInt8 :=
  encodeUIntLE 2 message.partitionId
    ++ (Alpha.encode message.pad6)

def decode (bytes : List UInt8) : Option (PartitionGrpComp × List UInt8) := do
  let (partitionId, bytes) ← decodeUIntLE 2 bytes
  let (pad6, bytes) ← Alpha.decode 6 bytes
  pure ({ partitionId, pad6 }, bytes)

@[simp] theorem encode_length (message : PartitionGrpComp) : (encode message).length = 8 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length]

theorem encode_length_pos (message : PartitionGrpComp) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : PartitionGrpComp) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end PartitionGrpComp

/-- Partition List Notification -/
structure PartitionListNotification where
  pad2 : Alpha 2
  notifHeaderComp : NotifHeaderComp
  pad7 : Alpha 7
  partitionGrpComp : Bounded 1 PartitionGrpComp
  deriving DecidableEq, Repr

namespace PartitionListNotification

def encode (message : PartitionListNotification) : List UInt8 :=
  Alpha.encode message.pad2
    ++ (NotifHeaderComp.encode message.notifHeaderComp
    ++ (encodeUInt 1 (BitVec.ofNat (8 * 1) message.partitionGrpComp.val.length)
    ++ (Alpha.encode message.pad7
    ++ (encodeMany PartitionGrpComp.encode message.partitionGrpComp.val))))

def decode (bytes : List UInt8) : Option (PartitionListNotification × List UInt8) := do
  let (pad2, bytes) ← Alpha.decode 2 bytes
  let (notifHeaderComp, bytes) ← NotifHeaderComp.decode bytes
  let (noPartitions, bytes) ← decodeUInt 1 bytes
  let (pad7, bytes) ← Alpha.decode 7 bytes
  let (partitionGrpComp_, bytes) ← decodeMany PartitionGrpComp.decode noPartitions.toNat bytes
  if fits_partitionGrpComp : partitionGrpComp_.length < 256 ^ 1 then
    pure ({ pad2, notifHeaderComp, pad7, partitionGrpComp := ⟨partitionGrpComp_, fits_partitionGrpComp⟩ }, bytes)
  else none

theorem encode_length_pos (message : PartitionListNotification) : (encode message).length > 0 := by
  unfold encode
  simp only [Alpha.encode_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : PartitionListNotification) : (encode message).length ≤ 2058 := by
  have bound_partitionGrpComp := message.partitionGrpComp.length_lt
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, Alpha.encode_length, NotifHeaderComp.encode_length, encodeUInt_length, encodeMany_length_const PartitionGrpComp.encode 8 PartitionGrpComp.encode_length]
  omega

@[simp] theorem decode_encode (message : PartitionListNotification) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, NotifHeaderComp.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [decodeMany_bounded 1 PartitionGrpComp.encode PartitionGrpComp.decode PartitionGrpComp.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.partitionGrpComp.length_lt]
  rfl

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : PartitionListNotification) : decode (encode message) = some (message, []) :=
  List.append_nil (encode message) ▸ decode_encode message []

end PartitionListNotification

/-- Reject -/
structure Reject where
  pad2 : Alpha 2
  responseHeaderComp : ResponseHeaderComp
  sessionRejectReason : BitVec 32
  sessionStatus : BitVec 8
  varText : Bounded 2 UInt8
  alignmentPadding : Capped 7
  deriving DecidableEq, Repr

namespace Reject

def encode (message : Reject) : List UInt8 :=
  Alpha.encode message.pad2
    ++ (ResponseHeaderComp.encode message.responseHeaderComp
    ++ (encodeUIntLE 4 message.sessionRejectReason
    ++ (encodeUIntLE 2 (BitVec.ofNat (8 * 2) message.varText.val.length)
    ++ (encodeUInt 1 message.sessionStatus
    ++ (encodeMany Byte.encode message.varText.val
    ++ (message.alignmentPadding.val))))))

def decode (bytes : List UInt8) : Option Reject := do
  let (pad2, bytes) ← Alpha.decode 2 bytes
  let (responseHeaderComp, bytes) ← ResponseHeaderComp.decode bytes
  let (sessionRejectReason, bytes) ← decodeUIntLE 4 bytes
  let (varTextLen, bytes) ← decodeUIntLE 2 bytes
  let (sessionStatus, bytes) ← decodeUInt 1 bytes
  let (varText_, bytes) ← decodeMany Byte.decode varTextLen.toNat bytes
  let alignmentPadding_ := bytes
  if fits_varText : varText_.length < 256 ^ 2 then
    if fits_alignmentPadding : alignmentPadding_.length ≤ 7 then
      pure { pad2, responseHeaderComp, sessionRejectReason, sessionStatus, varText := ⟨varText_, fits_varText⟩, alignmentPadding := ⟨alignmentPadding_, fits_alignmentPadding⟩ }
    else none
  else none

theorem encode_length_pos (message : Reject) : (encode message).length > 0 := by
  unfold encode
  simp only [Alpha.encode_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : Reject) : (encode message).length ≤ 65575 := by
  have bound_varText := message.varText.length_lt
  have bound_alignmentPadding := message.alignmentPadding.length_le
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, Alpha.encode_length, ResponseHeaderComp.encode_length, encodeUIntLE_length, encodeUInt_length, encodeMany_length_const Byte.encode 1 Byte.encode_length]
  omega

theorem decode_encode (message : Reject) : decode (encode message) = some message := by
  unfold decode encode
  rw [Alpha.decode_encode, some_bind]
  dsimp only
  rw [ResponseHeaderComp.decode_encode, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeMany_bounded 2 Byte.encode Byte.decode Byte.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.varText.length_lt, dite_eq_left message.alignmentPadding.length_le]
  rfl

end Reject

/-- Sessions Grp Comp: 48 bytes -/
structure SessionsGrpComp where
  partyIdSessionId : BitVec 32
  partyIdExecutingUnit : BitVec 32
  partyIdSponsoredAccessUnit : BitVec 32
  sessionMode : BitVec 8
  partyExecutingFirm : Alpha 5
  partySponsoredAccessUnit : Alpha 30
  deriving DecidableEq, Repr

namespace SessionsGrpComp

def encode (message : SessionsGrpComp) : List UInt8 :=
  encodeUIntLE 4 message.partyIdSessionId
    ++ (encodeUIntLE 4 message.partyIdExecutingUnit
    ++ (encodeUIntLE 4 message.partyIdSponsoredAccessUnit
    ++ (encodeUInt 1 message.sessionMode
    ++ (Alpha.encode message.partyExecutingFirm
    ++ (Alpha.encode message.partySponsoredAccessUnit)))))

def decode (bytes : List UInt8) : Option (SessionsGrpComp × List UInt8) := do
  let (partyIdSessionId, bytes) ← decodeUIntLE 4 bytes
  let (partyIdExecutingUnit, bytes) ← decodeUIntLE 4 bytes
  let (partyIdSponsoredAccessUnit, bytes) ← decodeUIntLE 4 bytes
  let (sessionMode, bytes) ← decodeUInt 1 bytes
  let (partyExecutingFirm, bytes) ← Alpha.decode 5 bytes
  let (partySponsoredAccessUnit, bytes) ← Alpha.decode 30 bytes
  pure ({ partyIdSessionId, partyIdExecutingUnit, partyIdSponsoredAccessUnit, sessionMode, partyExecutingFirm, partySponsoredAccessUnit }, bytes)

@[simp] theorem encode_length (message : SessionsGrpComp) : (encode message).length = 48 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, encodeUInt_length, Alpha.encode_length]

theorem encode_length_pos (message : SessionsGrpComp) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SessionsGrpComp) (rest : List UInt8) :
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
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end SessionsGrpComp

/-- Session List Notification -/
structure SessionListNotification where
  pad2 : Alpha 2
  notifHeaderComp : NotifHeaderComp
  pad6 : Alpha 6
  sessionsGrpComp : Bounded 2 SessionsGrpComp
  deriving DecidableEq, Repr

namespace SessionListNotification

def encode (message : SessionListNotification) : List UInt8 :=
  Alpha.encode message.pad2
    ++ (NotifHeaderComp.encode message.notifHeaderComp
    ++ (encodeUIntLE 2 (BitVec.ofNat (8 * 2) message.sessionsGrpComp.val.length)
    ++ (Alpha.encode message.pad6
    ++ (encodeMany SessionsGrpComp.encode message.sessionsGrpComp.val))))

def decode (bytes : List UInt8) : Option (SessionListNotification × List UInt8) := do
  let (pad2, bytes) ← Alpha.decode 2 bytes
  let (notifHeaderComp, bytes) ← NotifHeaderComp.decode bytes
  let (noSessions, bytes) ← decodeUIntLE 2 bytes
  let (pad6, bytes) ← Alpha.decode 6 bytes
  let (sessionsGrpComp_, bytes) ← decodeMany SessionsGrpComp.decode noSessions.toNat bytes
  if fits_sessionsGrpComp : sessionsGrpComp_.length < 256 ^ 2 then
    pure ({ pad2, notifHeaderComp, pad6, sessionsGrpComp := ⟨sessionsGrpComp_, fits_sessionsGrpComp⟩ }, bytes)
  else none

theorem encode_length_pos (message : SessionListNotification) : (encode message).length > 0 := by
  unfold encode
  simp only [Alpha.encode_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : SessionListNotification) : (encode message).length ≤ 3145698 := by
  have bound_sessionsGrpComp := message.sessionsGrpComp.length_lt
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, Alpha.encode_length, NotifHeaderComp.encode_length, encodeUIntLE_length, encodeMany_length_const SessionsGrpComp.encode 48 SessionsGrpComp.encode_length]
  omega

@[simp] theorem decode_encode (message : SessionListNotification) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, NotifHeaderComp.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [decodeMany_bounded 2 SessionsGrpComp.encode SessionsGrpComp.decode SessionsGrpComp.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.sessionsGrpComp.length_lt]
  rfl

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : SessionListNotification) : decode (encode message) = some (message, []) :=
  List.append_nil (encode message) ▸ decode_encode message []

end SessionListNotification

/-- Session Status Broadcast: 34 bytes -/
structure SessionStatusBroadcast where
  pad2 : Alpha 2
  rbcHeaderComp : RbcHeaderComp
  tradeDate : BitVec 32
  marketSegmentId : BitVec 32
  tradSesEvent : BitVec 8
  pad7 : Alpha 7
  deriving DecidableEq, Repr

namespace SessionStatusBroadcast

def encode (message : SessionStatusBroadcast) : List UInt8 :=
  Alpha.encode message.pad2
    ++ (RbcHeaderComp.encode message.rbcHeaderComp
    ++ (encodeUIntLE 4 message.tradeDate
    ++ (encodeUIntLE 4 message.marketSegmentId
    ++ (encodeUInt 1 message.tradSesEvent
    ++ (Alpha.encode message.pad7)))))

def decode (bytes : List UInt8) : Option (SessionStatusBroadcast × List UInt8) := do
  let (pad2, bytes) ← Alpha.decode 2 bytes
  let (rbcHeaderComp, bytes) ← RbcHeaderComp.decode bytes
  let (tradeDate, bytes) ← decodeUIntLE 4 bytes
  let (marketSegmentId, bytes) ← decodeUIntLE 4 bytes
  let (tradSesEvent, bytes) ← decodeUInt 1 bytes
  let (pad7, bytes) ← Alpha.decode 7 bytes
  pure ({ pad2, rbcHeaderComp, tradeDate, marketSegmentId, tradSesEvent, pad7 }, bytes)

@[simp] theorem encode_length (message : SessionStatusBroadcast) : (encode message).length = 34 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, RbcHeaderComp.encode_length, encodeUIntLE_length, encodeUInt_length]

theorem encode_length_pos (message : SessionStatusBroadcast) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SessionStatusBroadcast) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, RbcHeaderComp.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : SessionStatusBroadcast) : decode (encode message) = some (message, []) :=
  List.append_nil (encode message) ▸ decode_encode message []

end SessionStatusBroadcast

/-- Any Server Payload, selected by Template Id -/
inductive ServerPayload where
  | deleteOrderBroadcast (message : DeleteOrderBroadcast) -- 10902
  | forcedLogoutNotification (message : ForcedLogoutNotification) -- 10012
  | heartbeatNotification (message : HeartbeatNotification) -- 10023
  | logonResponse (message : LogonResponse) -- 10001
  | logoutResponse (message : LogoutResponse) -- 10003
  | orderExecReportBroadcast (message : OrderExecReportBroadcast) -- 10901
  | partitionListNotification (message : PartitionListNotification) -- 10037
  | reject (message : Reject) -- 10010
  | sessionListNotification (message : SessionListNotification) -- 10036
  | sessionStatusBroadcast (message : SessionStatusBroadcast) -- 10903
  deriving DecidableEq, Repr

namespace ServerPayload

/-- The Template Id each message is sent under -/
def tag : ServerPayload → BitVec 16
  | .deleteOrderBroadcast _ => 10902
  | .forcedLogoutNotification _ => 10012
  | .heartbeatNotification _ => 10023
  | .logonResponse _ => 10001
  | .logoutResponse _ => 10003
  | .orderExecReportBroadcast _ => 10901
  | .partitionListNotification _ => 10037
  | .reject _ => 10010
  | .sessionListNotification _ => 10036
  | .sessionStatusBroadcast _ => 10903

def encode : ServerPayload → List UInt8
  | .deleteOrderBroadcast message => DeleteOrderBroadcast.encode message
  | .forcedLogoutNotification message => ForcedLogoutNotification.encode message
  | .heartbeatNotification message => HeartbeatNotification.encode message
  | .logonResponse message => LogonResponse.encode message
  | .logoutResponse message => LogoutResponse.encode message
  | .orderExecReportBroadcast message => OrderExecReportBroadcast.encode message
  | .partitionListNotification message => PartitionListNotification.encode message
  | .reject message => Reject.encode message
  | .sessionListNotification message => SessionListNotification.encode message
  | .sessionStatusBroadcast message => SessionStatusBroadcast.encode message

/-- Decoded from the whole of the frame: a message that reads to its end takes it all, any other must leave nothing -/
def decode (tag : BitVec 16) (bytes : List UInt8) : Option ServerPayload :=
  if tag = 10902 then (DeleteOrderBroadcast.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.deleteOrderBroadcast message) else none
  else if tag = 10012 then (ForcedLogoutNotification.decode bytes).map fun message => .forcedLogoutNotification message
  else if tag = 10023 then (HeartbeatNotification.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.heartbeatNotification message) else none
  else if tag = 10001 then (LogonResponse.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.logonResponse message) else none
  else if tag = 10003 then (LogoutResponse.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.logoutResponse message) else none
  else if tag = 10901 then (OrderExecReportBroadcast.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.orderExecReportBroadcast message) else none
  else if tag = 10037 then (PartitionListNotification.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.partitionListNotification message) else none
  else if tag = 10010 then (Reject.decode bytes).map fun message => .reject message
  else if tag = 10036 then (SessionListNotification.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.sessionListNotification message) else none
  else if tag = 10903 then (SessionStatusBroadcast.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.sessionStatusBroadcast message) else none
  else none

theorem decode_encode (message : ServerPayload) :
    decode (tag message) (encode message) = some message := by
  cases message with
  | deleteOrderBroadcast message => simp [decode, encode, tag, DeleteOrderBroadcast.decode_encode_nil]
  | forcedLogoutNotification message => simp [decode, encode, tag, ForcedLogoutNotification.decode_encode]
  | heartbeatNotification message => simp [decode, encode, tag, HeartbeatNotification.decode_encode_nil]
  | logonResponse message => simp [decode, encode, tag, LogonResponse.decode_encode_nil]
  | logoutResponse message => simp [decode, encode, tag, LogoutResponse.decode_encode_nil]
  | orderExecReportBroadcast message => simp [decode, encode, tag, OrderExecReportBroadcast.decode_encode_nil]
  | partitionListNotification message => simp [decode, encode, tag, PartitionListNotification.decode_encode_nil]
  | reject message => simp [decode, encode, tag, Reject.decode_encode]
  | sessionListNotification message => simp [decode, encode, tag, SessionListNotification.decode_encode_nil]
  | sessionStatusBroadcast message => simp [decode, encode, tag, SessionStatusBroadcast.decode_encode_nil]

end ServerPayload

/-- Server Message -/
structure ServerMessage where
  serverPayload : ServerPayload
  deriving DecidableEq, Repr

namespace ServerMessage

def encodeBody (message : ServerMessage) : List UInt8 :=
  encodeUIntLE 2 (ServerPayload.tag message.serverPayload)
    ++ (ServerPayload.encode message.serverPayload)

def decodeBody (bytes : List UInt8) : Option ServerMessage := do
  let (templateId, bytes) ← decodeUIntLE 2 bytes
  let serverPayload ← ServerPayload.decode templateId bytes
  pure { serverPayload }

theorem decodeBody_encodeBody (message : ServerMessage) : decodeBody (encodeBody message) = some message := by
  unfold decodeBody encodeBody
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [ServerPayload.decode_encode, some_bind]
  rfl

/-- Every body fits the length prefix -/
theorem encodeBody_length_lt (message : ServerMessage) : (encodeBody message).length + 4 < 256 ^ 4 := by
  unfold encodeBody
  cases message.serverPayload with
  | deleteOrderBroadcast inner =>
    have bound_inner := DeleteOrderBroadcast.encode_length_le inner
    simp only [ServerPayload.encode, List.length_append, encodeUIntLE_length]
    omega
  | forcedLogoutNotification inner =>
    have bound_inner := ForcedLogoutNotification.encode_length_le inner
    simp only [ServerPayload.encode, List.length_append, encodeUIntLE_length]
    omega
  | heartbeatNotification inner =>
    simp only [ServerPayload.encode, List.length_append, encodeUIntLE_length, HeartbeatNotification.encode_length]
    omega
  | logonResponse inner =>
    simp only [ServerPayload.encode, List.length_append, encodeUIntLE_length, LogonResponse.encode_length]
    omega
  | logoutResponse inner =>
    simp only [ServerPayload.encode, List.length_append, encodeUIntLE_length, LogoutResponse.encode_length]
    omega
  | orderExecReportBroadcast inner =>
    have bound_inner := OrderExecReportBroadcast.encode_length_le inner
    simp only [ServerPayload.encode, List.length_append, encodeUIntLE_length]
    omega
  | partitionListNotification inner =>
    have bound_inner := PartitionListNotification.encode_length_le inner
    simp only [ServerPayload.encode, List.length_append, encodeUIntLE_length]
    omega
  | reject inner =>
    have bound_inner := Reject.encode_length_le inner
    simp only [ServerPayload.encode, List.length_append, encodeUIntLE_length]
    omega
  | sessionListNotification inner =>
    have bound_inner := SessionListNotification.encode_length_le inner
    simp only [ServerPayload.encode, List.length_append, encodeUIntLE_length]
    omega
  | sessionStatusBroadcast inner =>
    simp only [ServerPayload.encode, List.length_append, encodeUIntLE_length, SessionStatusBroadcast.encode_length]
    omega

/-- Size rule: Body Len counts the bytes after it plus 4, so it is written from the body and checked on decode -/
def encode : ServerMessage → List UInt8 :=
  encodeFramedLE 4 4 encodeBody

def decode : List UInt8 → Option (ServerMessage × List UInt8) :=
  decodeFramedAllLE 4 4 decodeBody

@[simp] theorem decode_encode (message : ServerMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) :=
  decodeFramedAllLE_encodeFramedLE 4 4 encodeBody decodeBody message (decodeBody_encodeBody message) (encodeBody_length_lt message) rest

theorem encode_length_pos (message : ServerMessage) : (encode message).length > 0 := by
  unfold encode
  rw [encodeFramedLE_length]
  omega

end ServerMessage

/-- Server Packet -/
structure ServerPacket where
  serverMessage : List ServerMessage
  deriving DecidableEq, Repr

namespace ServerPacket

def encode (message : ServerPacket) : List UInt8 :=
  encodeMany ServerMessage.encode message.serverMessage

def decode (bytes : List UInt8) : Option ServerPacket := do
  let serverMessage ← decodeAll ServerMessage.decode bytes.length bytes
  pure { serverMessage }

theorem decode_encode (message : ServerPacket) : decode (encode message) = some message := by
  unfold decode encode
  rw [decodeAll_encodeMany ServerMessage.encode ServerMessage.decode ServerMessage.decode_encode ServerMessage.encode_length_pos message.serverMessage _ (encodeMany_length_ge ServerMessage.encode ServerMessage.encode_length_pos message.serverMessage), some_bind]
  rfl

end ServerPacket

end Omi.EurexT7EdciFbeV141Server
