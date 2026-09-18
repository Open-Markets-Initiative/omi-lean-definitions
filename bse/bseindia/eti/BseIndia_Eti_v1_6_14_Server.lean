import Omi.Wire

/-!
# BSE Limited Enhanced Trading Interface v1.6.14

Generated from the binary model, with the proofs the model's rules call for: every record
decodes back to what was encoded; a message dispatch selects the message its type names;
a count is written from the list it counts; a length prefix is written from the bytes it frames;
and a packet read to the end of its data decodes to the messages that were written.

Note: Alignment Padding pads to a 8 byte boundary: it is read as the bytes left to the end of the frame, fewer than 8, and the frame's length is trusted to keep the boundary.

Note: Broadcast Error Notification is not framed: its length Body Len is not an integer it reads.

Note: Debt Inquiry Response is not framed: its length Body Len is not an integer it reads.

Note: Delete All Order Broadcast is not framed: its length Body Len is not an integer it reads.

Note: Delete All Order Nr Response is not framed: its length Body Len is not an integer it reads.

Note: Delete All Order Quote Event Broadcast is not framed: its length Body Len is not an integer it reads.

Note: Delete All Order Response is not framed: its length Body Len is not an integer it reads.

Note: Delete All Quote Broadcast is not framed: its length Body Len is not an integer it reads.

Note: Delete All Quote Response is not framed: its length Body Len is not an integer it reads.

Note: Delete Order Broadcast is not framed: its length Body Len is not an integer it reads.

Note: Delete Order Nr Response is not framed: its length Body Len is not an integer it reads.

Note: Delete Order Response is not framed: its length Body Len is not an integer it reads.

Note: Alignment Padding pads to a 8 byte boundary: it is read as the bytes left to the end of the frame, fewer than 8, and the frame's length is trusted to keep the boundary.

Note: Forced Logout Notification is not framed: its length Body Len is not an integer it reads.

Note: Gateway Response is not framed: its length Body Len is not an integer it reads.

Note: Gw Order Acknowledgement is not framed: its length Body Len is not an integer it reads.

Note: Heartbeat Notification is not framed: its length Body Len is not an integer it reads.

Note: Inquire Session List Response is not framed: its length Body Len is not an integer it reads.

Note: Logon Response is not framed: its length Body Len is not an integer it reads.

Note: Logout Response is not framed: its length Body Len is not an integer it reads.

Note: Mass Quote Response is not framed: its length Body Len is not an integer it reads.

Note: Modify Order Nr Response is not framed: its length Body Len is not an integer it reads.

Note: Modify Order Response is not framed: its length Body Len is not an integer it reads.

Note: Multi Leg Exec Report Broadcast is not framed: its length Body Len is not an integer it reads.

Note: Multi Leg Exec Response is not framed: its length Body Len is not an integer it reads.

Note: Alignment Padding pads to a 8 byte boundary: it is read as the bytes left to the end of the frame, fewer than 8, and the frame's length is trusted to keep the boundary.

Note: Multi Leg Order Reject is not framed: its length Body Len is not an integer it reads.

Note: New Order Nr Response is not framed: its length Body Len is not an integer it reads.

Note: New Order Response is not framed: its length Body Len is not an integer it reads.

Note: Alignment Padding pads to a 8 byte boundary: it is read as the bytes left to the end of the frame, fewer than 8, and the frame's length is trusted to keep the boundary.

Note: News Broadcast is not framed: its length Body Len is not an integer it reads.

Note: Order Exec Notification is not framed: its length Body Len is not an integer it reads.

Note: Order Exec Report Broadcast is not framed: its length Body Len is not an integer it reads.

Note: Order Exec Response is not framed: its length Body Len is not an integer it reads.

Note: Quote Exec Report Broadcast is not framed: its length Body Len is not an integer it reads.

Note: Quote Execution Report is not framed: its length Body Len is not an integer it reads.

Note: Alignment Padding pads to a 8 byte boundary: it is read as the bytes left to the end of the frame, fewer than 8, and the frame's length is trusted to keep the boundary.

Note: Reject is not framed: its length Body Len is not an integer it reads.

Note: Retransmit Me Message Response is not framed: its length Body Len is not an integer it reads.

Note: Retransmit Response is not framed: its length Body Len is not an integer it reads.

Note: Alignment Padding pads to a 8 byte boundary: it is read as the bytes left to the end of the frame, fewer than 8, and the frame's length is trusted to keep the boundary.

Note: Risk Collateral Alert Admin Broadcast is not framed: its length Body Len is not an integer it reads.

Note: Alignment Padding pads to a 8 byte boundary: it is read as the bytes left to the end of the frame, fewer than 8, and the frame's length is trusted to keep the boundary.

Note: Risk Collateral Alert Broadcast is not framed: its length Body Len is not an integer it reads.

Note: Risk Notification Broadcast is not framed: its length Body Len is not an integer it reads.

Note: Service Availability Broadcast is not framed: its length Body Len is not an integer it reads.

Note: Session Password Change Response is not framed: its length Body Len is not an integer it reads.

Note: Alignment Padding pads to a 8 byte boundary: it is read as the bytes left to the end of the frame, fewer than 8, and the frame's length is trusted to keep the boundary.

Note: Session Registration Response is not framed: its length Body Len is not an integer it reads.

Note: Subscribe Response is not framed: its length Body Len is not an integer it reads.

Note: Tm Trading Session Status Broadcast is not framed: its length Body Len is not an integer it reads.

Note: Throttle Update Notification is not framed: its length Body Len is not an integer it reads.

Note: Trade Broadcast is not framed: its length Body Len is not an integer it reads.

Note: Trade Enhancement Broadcast is not framed: its length Body Len is not an integer it reads.

Note: Trading Session Status Broadcast is not framed: its length Body Len is not an integer it reads.

Note: Unsubscribe Response is not framed: its length Body Len is not an integer it reads.

Note: User Login Response is not framed: its length Body Len is not an integer it reads.

Note: User Logout Response is not framed: its length Body Len is not an integer it reads.

Note: User Password Change Response is not framed: its length Body Len is not an integer it reads.

Text fields are kept byte for byte, padding included, so what is decoded encodes back unchanged.
Prices with implied decimals are proven as the integers on the wire.
-/

namespace Omi.BseBseindiaEtiFbeV1614Server

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
  [0x30, 0x34, 0x35, 0x36, 0x39, 0x44, 0x4C, 0x46, 0x4D, 0x4E, 0x58, 0x59]

inductive ExecType where
  | new -- New
  | canceled -- Canceled
  | replaced -- Replaced
  | pendingCancele -- Pending Cancele
  | suspended -- Suspended
  | restated -- Restated
  | triggered -- Triggered
  | trade -- Trade
  | rrmAccept -- Rrm Accept
  | rrmReject -- Rrm Reject
  | provAccept -- Prov Accept
  | provReject -- Prov Reject
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
  | .rrmAccept => 0x4D
  | .rrmReject => 0x4E
  | .provAccept => 0x58
  | .provReject => 0x59
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
  else if byte = 0x46 then .trade
  else if byte = 0x4D then .rrmAccept
  else if byte = 0x4E then .rrmReject
  else if byte = 0x58 then .provAccept
  else .provReject

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
  | rrmAccept => decide
  | rrmReject => decide
  | provAccept => decide
  | provReject => decide
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

/-- List Update Action: one byte code -/
def ListUpdateAction.codes : List UInt8 :=
  [0x41, 0x44]

inductive ListUpdateAction where
  | add -- Add
  | delete -- Delete
  | unlisted (byte : { byte : UInt8 // byte ∉ ListUpdateAction.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace ListUpdateAction

def toByte : ListUpdateAction → UInt8
  | .add => 0x41
  | .delete => 0x44
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : ListUpdateAction :=
  if byte = 0x41 then .add
  else .delete

def ofByte (byte : UInt8) : ListUpdateAction :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : ListUpdateAction) : ofByte value.toByte = value := by
  cases value with
  | add => decide
  | delete => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : ListUpdateAction) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (ListUpdateAction × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : ListUpdateAction) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : ListUpdateAction) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end ListUpdateAction

/-- Status: one byte code -/
def Status.codes : List UInt8 :=
  [0x4E, 0x59]

inductive Status where
  | reject -- Reject
  | accept -- Accept
  | unlisted (byte : { byte : UInt8 // byte ∉ Status.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace Status

def toByte : Status → UInt8
  | .reject => 0x4E
  | .accept => 0x59
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : Status :=
  if byte = 0x4E then .reject
  else .accept

def ofByte (byte : UInt8) : Status :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : Status) : ofByte value.toByte = value := by
  cases value with
  | reject => decide
  | accept => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : Status) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (Status × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : Status) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : Status) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end Status

/-- Order Category: one byte code -/
def OrderCategory.codes : List UInt8 :=
  [0x31, 0x32, 0x33]

inductive OrderCategory where
  | order -- Order
  | quote -- Quote
  | multiLegOrder -- Multi Leg Order
  | unlisted (byte : { byte : UInt8 // byte ∉ OrderCategory.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace OrderCategory

def toByte : OrderCategory → UInt8
  | .order => 0x31
  | .quote => 0x32
  | .multiLegOrder => 0x33
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : OrderCategory :=
  if byte = 0x31 then .order
  else if byte = 0x32 then .quote
  else .multiLegOrder

def ofByte (byte : UInt8) : OrderCategory :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : OrderCategory) : ofByte value.toByte = value := by
  cases value with
  | order => decide
  | quote => decide
  | multiLegOrder => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : OrderCategory) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (OrderCategory × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : OrderCategory) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : OrderCategory) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end OrderCategory

/-- Auto Accept Indicator: one byte code -/
def AutoAcceptIndicator.codes : List UInt8 :=
  [0x59, 0x4E]

inductive AutoAcceptIndicator where
  | accepted -- Accepted
  | rejected -- Rejected
  | unlisted (byte : { byte : UInt8 // byte ∉ AutoAcceptIndicator.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace AutoAcceptIndicator

def toByte : AutoAcceptIndicator → UInt8
  | .accepted => 0x59
  | .rejected => 0x4E
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : AutoAcceptIndicator :=
  if byte = 0x59 then .accepted
  else .rejected

def ofByte (byte : UInt8) : AutoAcceptIndicator :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : AutoAcceptIndicator) : ofByte value.toByte = value := by
  cases value with
  | accepted => decide
  | rejected => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : AutoAcceptIndicator) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (AutoAcceptIndicator × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : AutoAcceptIndicator) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : AutoAcceptIndicator) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end AutoAcceptIndicator

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

/-- Broadcast Error Notification -/
structure BroadcastErrorNotification where
  filler4 : Alpha 2
  notifHeaderComp : NotifHeaderComp
  applIdStatus : BitVec 32
  refApplSubId : BitVec 32
  refApplId : BitVec 8
  sessionStatus : BitVec 8
  pad4 : Alpha 4
  varText : Bounded 2 UInt8
  alignmentPadding : Capped 7
  deriving DecidableEq, Repr

namespace BroadcastErrorNotification

def encode (message : BroadcastErrorNotification) : List UInt8 :=
  Alpha.encode message.filler4
    ++ (NotifHeaderComp.encode message.notifHeaderComp
    ++ (encodeUIntLE 4 message.applIdStatus
    ++ (encodeUIntLE 4 message.refApplSubId
    ++ (encodeUIntLE 2 (BitVec.ofNat (8 * 2) message.varText.val.length)
    ++ (encodeUInt 1 message.refApplId
    ++ (encodeUInt 1 message.sessionStatus
    ++ (Alpha.encode message.pad4
    ++ (encodeMany Byte.encode message.varText.val
    ++ (message.alignmentPadding.val)))))))))

def decode (bytes : List UInt8) : Option BroadcastErrorNotification := do
  let (filler4, bytes) ← Alpha.decode 2 bytes
  let (notifHeaderComp, bytes) ← NotifHeaderComp.decode bytes
  let (applIdStatus, bytes) ← decodeUIntLE 4 bytes
  let (refApplSubId, bytes) ← decodeUIntLE 4 bytes
  let (varTextLen, bytes) ← decodeUIntLE 2 bytes
  let (refApplId, bytes) ← decodeUInt 1 bytes
  let (sessionStatus, bytes) ← decodeUInt 1 bytes
  let (pad4, bytes) ← Alpha.decode 4 bytes
  let (varText_, bytes) ← decodeMany Byte.decode varTextLen.toNat bytes
  let alignmentPadding_ := bytes
  if fits_varText : varText_.length < 256 ^ 2 then
    if fits_alignmentPadding : alignmentPadding_.length ≤ 7 then
      pure { filler4, notifHeaderComp, applIdStatus, refApplSubId, refApplId, sessionStatus, pad4, varText := ⟨varText_, fits_varText⟩, alignmentPadding := ⟨alignmentPadding_, fits_alignmentPadding⟩ }
    else none
  else none

theorem encode_length_pos (message : BroadcastErrorNotification) : (encode message).length > 0 := by
  unfold encode
  simp only [Alpha.encode_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : BroadcastErrorNotification) : (encode message).length ≤ 65568 := by
  have bound_varText := message.varText.length_lt
  have bound_alignmentPadding := message.alignmentPadding.length_le
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, Alpha.encode_length, NotifHeaderComp.encode_length, encodeUIntLE_length, encodeUInt_length, encodeMany_length_const Byte.encode 1 Byte.encode_length]
  omega

theorem decode_encode (message : BroadcastErrorNotification) : decode (encode message) = some message := by
  unfold decode encode
  rw [Alpha.decode_encode, some_bind]
  dsimp only
  rw [NotifHeaderComp.decode_encode, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  dsimp only
  rw [decodeMany_bounded 2 Byte.encode Byte.decode Byte.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.varText.length_lt, dite_eq_left message.alignmentPadding.length_le]
  rfl

end BroadcastErrorNotification

/-- Nr Response Header Me Comp: 56 bytes -/
structure NrResponseHeaderMeComp where
  requestTime : BitVec 64
  requestOut : BitVec 64
  trdRegTsTimeIn : BitVec 64
  trdRegTsTimeOut : BitVec 64
  responseIn : BitVec 64
  sendingTime : BitVec 64
  msgSeqNum : BitVec 32
  lastFragment : BitVec 8
  pad3 : Alpha 3
  deriving DecidableEq, Repr

namespace NrResponseHeaderMeComp

def encode (message : NrResponseHeaderMeComp) : List UInt8 :=
  encodeUIntLE 8 message.requestTime
    ++ (encodeUIntLE 8 message.requestOut
    ++ (encodeUIntLE 8 message.trdRegTsTimeIn
    ++ (encodeUIntLE 8 message.trdRegTsTimeOut
    ++ (encodeUIntLE 8 message.responseIn
    ++ (encodeUIntLE 8 message.sendingTime
    ++ (encodeUIntLE 4 message.msgSeqNum
    ++ (encodeUInt 1 message.lastFragment
    ++ (Alpha.encode message.pad3))))))))

def decode (bytes : List UInt8) : Option (NrResponseHeaderMeComp × List UInt8) := do
  let (requestTime, bytes) ← decodeUIntLE 8 bytes
  let (requestOut, bytes) ← decodeUIntLE 8 bytes
  let (trdRegTsTimeIn, bytes) ← decodeUIntLE 8 bytes
  let (trdRegTsTimeOut, bytes) ← decodeUIntLE 8 bytes
  let (responseIn, bytes) ← decodeUIntLE 8 bytes
  let (sendingTime, bytes) ← decodeUIntLE 8 bytes
  let (msgSeqNum, bytes) ← decodeUIntLE 4 bytes
  let (lastFragment, bytes) ← decodeUInt 1 bytes
  let (pad3, bytes) ← Alpha.decode 3 bytes
  pure ({ requestTime, requestOut, trdRegTsTimeIn, trdRegTsTimeOut, responseIn, sendingTime, msgSeqNum, lastFragment, pad3 }, bytes)

@[simp] theorem encode_length (message : NrResponseHeaderMeComp) : (encode message).length = 56 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, encodeUInt_length, Alpha.encode_length]

theorem encode_length_pos (message : NrResponseHeaderMeComp) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : NrResponseHeaderMeComp) (rest : List UInt8) :
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
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end NrResponseHeaderMeComp

/-- Debt Inquiry Response: 114 bytes -/
structure DebtInquiryResponse where
  filler4 : Alpha 2
  nrResponseHeaderMeComp : NrResponseHeaderMeComp
  underlyingPx : BitVec 64
  yield : BitVec 64
  accruedInterestAmt : BitVec 64
  grossTradeAmt : BitVec 64
  underlyingDirtyPrice : BitVec 64
  securityId : BitVec 64
  orderQty : BitVec 32
  settlType : BitVec 32
  deriving DecidableEq, Repr

namespace DebtInquiryResponse

def encode (message : DebtInquiryResponse) : List UInt8 :=
  Alpha.encode message.filler4
    ++ (NrResponseHeaderMeComp.encode message.nrResponseHeaderMeComp
    ++ (encodeUIntLE 8 message.underlyingPx
    ++ (encodeUIntLE 8 message.yield
    ++ (encodeUIntLE 8 message.accruedInterestAmt
    ++ (encodeUIntLE 8 message.grossTradeAmt
    ++ (encodeUIntLE 8 message.underlyingDirtyPrice
    ++ (encodeUIntLE 8 message.securityId
    ++ (encodeUIntLE 4 message.orderQty
    ++ (encodeUIntLE 4 message.settlType)))))))))

def decode (bytes : List UInt8) : Option (DebtInquiryResponse × List UInt8) := do
  let (filler4, bytes) ← Alpha.decode 2 bytes
  let (nrResponseHeaderMeComp, bytes) ← NrResponseHeaderMeComp.decode bytes
  let (underlyingPx, bytes) ← decodeUIntLE 8 bytes
  let (yield, bytes) ← decodeUIntLE 8 bytes
  let (accruedInterestAmt, bytes) ← decodeUIntLE 8 bytes
  let (grossTradeAmt, bytes) ← decodeUIntLE 8 bytes
  let (underlyingDirtyPrice, bytes) ← decodeUIntLE 8 bytes
  let (securityId, bytes) ← decodeUIntLE 8 bytes
  let (orderQty, bytes) ← decodeUIntLE 4 bytes
  let (settlType, bytes) ← decodeUIntLE 4 bytes
  pure ({ filler4, nrResponseHeaderMeComp, underlyingPx, yield, accruedInterestAmt, grossTradeAmt, underlyingDirtyPrice, securityId, orderQty, settlType }, bytes)

@[simp] theorem encode_length (message : DebtInquiryResponse) : (encode message).length = 114 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, NrResponseHeaderMeComp.encode_length, encodeUIntLE_length]

theorem encode_length_pos (message : DebtInquiryResponse) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : DebtInquiryResponse) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, NrResponseHeaderMeComp.decode_encode, some_bind]
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

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : DebtInquiryResponse) : decode (encode message) = some (message, []) :=
  List.append_nil (encode message) ▸ decode_encode message []

end DebtInquiryResponse

/-- Rbc Header Me Comp: 48 bytes -/
structure RbcHeaderMeComp where
  trdRegTsTimeOut : BitVec 64
  sendingTime : BitVec 64
  applSubId : BitVec 32
  partitionId : BitVec 16
  applMsgId : Alpha 16
  applId : BitVec 8
  applResendFlag : BitVec 8
  lastFragment : BitVec 8
  pad7 : Alpha 7
  deriving DecidableEq, Repr

namespace RbcHeaderMeComp

def encode (message : RbcHeaderMeComp) : List UInt8 :=
  encodeUIntLE 8 message.trdRegTsTimeOut
    ++ (encodeUIntLE 8 message.sendingTime
    ++ (encodeUIntLE 4 message.applSubId
    ++ (encodeUIntLE 2 message.partitionId
    ++ (Alpha.encode message.applMsgId
    ++ (encodeUInt 1 message.applId
    ++ (encodeUInt 1 message.applResendFlag
    ++ (encodeUInt 1 message.lastFragment
    ++ (Alpha.encode message.pad7))))))))

def decode (bytes : List UInt8) : Option (RbcHeaderMeComp × List UInt8) := do
  let (trdRegTsTimeOut, bytes) ← decodeUIntLE 8 bytes
  let (sendingTime, bytes) ← decodeUIntLE 8 bytes
  let (applSubId, bytes) ← decodeUIntLE 4 bytes
  let (partitionId, bytes) ← decodeUIntLE 2 bytes
  let (applMsgId, bytes) ← Alpha.decode 16 bytes
  let (applId, bytes) ← decodeUInt 1 bytes
  let (applResendFlag, bytes) ← decodeUInt 1 bytes
  let (lastFragment, bytes) ← decodeUInt 1 bytes
  let (pad7, bytes) ← Alpha.decode 7 bytes
  pure ({ trdRegTsTimeOut, sendingTime, applSubId, partitionId, applMsgId, applId, applResendFlag, lastFragment, pad7 }, bytes)

@[simp] theorem encode_length (message : RbcHeaderMeComp) : (encode message).length = 48 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length, encodeUInt_length]

theorem encode_length_pos (message : RbcHeaderMeComp) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : RbcHeaderMeComp) (rest : List UInt8) :
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
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end RbcHeaderMeComp

/-- Not Affected Orders Grp Comp: 16 bytes -/
structure NotAffectedOrdersGrpComp where
  notAffectedOrderId : BitVec 64
  notAffOrigClOrdId : BitVec 64
  deriving DecidableEq, Repr

namespace NotAffectedOrdersGrpComp

def encode (message : NotAffectedOrdersGrpComp) : List UInt8 :=
  encodeUIntLE 8 message.notAffectedOrderId
    ++ (encodeUIntLE 8 message.notAffOrigClOrdId)

def decode (bytes : List UInt8) : Option (NotAffectedOrdersGrpComp × List UInt8) := do
  let (notAffectedOrderId, bytes) ← decodeUIntLE 8 bytes
  let (notAffOrigClOrdId, bytes) ← decodeUIntLE 8 bytes
  pure ({ notAffectedOrderId, notAffOrigClOrdId }, bytes)

@[simp] theorem encode_length (message : NotAffectedOrdersGrpComp) : (encode message).length = 16 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length]

theorem encode_length_pos (message : NotAffectedOrdersGrpComp) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : NotAffectedOrdersGrpComp) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end NotAffectedOrdersGrpComp

/-- Delete All Order Broadcast -/
structure DeleteAllOrderBroadcast where
  filler4 : Alpha 2
  rbcHeaderMeComp : RbcHeaderMeComp
  massActionReportId : BitVec 64
  securityId : BitVec 64
  marketSegmentId : BitVec 32
  targetPartyIdSessionId : BitVec 32
  targetPartyIdExecutingTrader : BitVec 32
  partyIdEnteringTrader : BitVec 32
  algoId : Alpha 16
  filler1 : Alpha 8
  filler2 : Alpha 4
  filler3 : Alpha 4
  partyIdEnteringFirm : BitVec 8
  massActionReason : BitVec 8
  execInst : BitVec 8
  pad3 : Alpha 3
  notAffectedOrdersGrpComp : Bounded 2 NotAffectedOrdersGrpComp
  deriving DecidableEq, Repr

namespace DeleteAllOrderBroadcast

def encode (message : DeleteAllOrderBroadcast) : List UInt8 :=
  Alpha.encode message.filler4
    ++ (RbcHeaderMeComp.encode message.rbcHeaderMeComp
    ++ (encodeUIntLE 8 message.massActionReportId
    ++ (encodeUIntLE 8 message.securityId
    ++ (encodeUIntLE 4 message.marketSegmentId
    ++ (encodeUIntLE 4 message.targetPartyIdSessionId
    ++ (encodeUIntLE 4 message.targetPartyIdExecutingTrader
    ++ (encodeUIntLE 4 message.partyIdEnteringTrader
    ++ (Alpha.encode message.algoId
    ++ (Alpha.encode message.filler1
    ++ (Alpha.encode message.filler2
    ++ (Alpha.encode message.filler3
    ++ (encodeUIntLE 2 (BitVec.ofNat (8 * 2) message.notAffectedOrdersGrpComp.val.length)
    ++ (encodeUInt 1 message.partyIdEnteringFirm
    ++ (encodeUInt 1 message.massActionReason
    ++ (encodeUInt 1 message.execInst
    ++ (Alpha.encode message.pad3
    ++ (encodeMany NotAffectedOrdersGrpComp.encode message.notAffectedOrdersGrpComp.val)))))))))))))))))

def decode (bytes : List UInt8) : Option (DeleteAllOrderBroadcast × List UInt8) := do
  let (filler4, bytes) ← Alpha.decode 2 bytes
  let (rbcHeaderMeComp, bytes) ← RbcHeaderMeComp.decode bytes
  let (massActionReportId, bytes) ← decodeUIntLE 8 bytes
  let (securityId, bytes) ← decodeUIntLE 8 bytes
  let (marketSegmentId, bytes) ← decodeUIntLE 4 bytes
  let (targetPartyIdSessionId, bytes) ← decodeUIntLE 4 bytes
  let (targetPartyIdExecutingTrader, bytes) ← decodeUIntLE 4 bytes
  let (partyIdEnteringTrader, bytes) ← decodeUIntLE 4 bytes
  let (algoId, bytes) ← Alpha.decode 16 bytes
  let (filler1, bytes) ← Alpha.decode 8 bytes
  let (filler2, bytes) ← Alpha.decode 4 bytes
  let (filler3, bytes) ← Alpha.decode 4 bytes
  let (noNotAffectedOrders, bytes) ← decodeUIntLE 2 bytes
  let (partyIdEnteringFirm, bytes) ← decodeUInt 1 bytes
  let (massActionReason, bytes) ← decodeUInt 1 bytes
  let (execInst, bytes) ← decodeUInt 1 bytes
  let (pad3, bytes) ← Alpha.decode 3 bytes
  let (notAffectedOrdersGrpComp_, bytes) ← decodeMany NotAffectedOrdersGrpComp.decode noNotAffectedOrders.toNat bytes
  if fits_notAffectedOrdersGrpComp : notAffectedOrdersGrpComp_.length < 256 ^ 2 then
    pure ({ filler4, rbcHeaderMeComp, massActionReportId, securityId, marketSegmentId, targetPartyIdSessionId, targetPartyIdExecutingTrader, partyIdEnteringTrader, algoId, filler1, filler2, filler3, partyIdEnteringFirm, massActionReason, execInst, pad3, notAffectedOrdersGrpComp := ⟨notAffectedOrdersGrpComp_, fits_notAffectedOrdersGrpComp⟩ }, bytes)
  else none

theorem encode_length_pos (message : DeleteAllOrderBroadcast) : (encode message).length > 0 := by
  unfold encode
  simp only [Alpha.encode_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : DeleteAllOrderBroadcast) : (encode message).length ≤ 1048682 := by
  have bound_notAffectedOrdersGrpComp := message.notAffectedOrdersGrpComp.length_lt
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, Alpha.encode_length, RbcHeaderMeComp.encode_length, encodeUIntLE_length, encodeUInt_length, encodeMany_length_const NotAffectedOrdersGrpComp.encode 16 NotAffectedOrdersGrpComp.encode_length]
  omega

@[simp] theorem decode_encode (message : DeleteAllOrderBroadcast) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, RbcHeaderMeComp.decode_encode, some_bind]
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
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [decodeMany_bounded 2 NotAffectedOrdersGrpComp.encode NotAffectedOrdersGrpComp.decode NotAffectedOrdersGrpComp.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.notAffectedOrdersGrpComp.length_lt]
  rfl

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : DeleteAllOrderBroadcast) : decode (encode message) = some (message, []) :=
  List.append_nil (encode message) ▸ decode_encode message []

end DeleteAllOrderBroadcast

/-- Delete All Order Nr Response: 66 bytes -/
structure DeleteAllOrderNrResponse where
  filler4 : Alpha 2
  nrResponseHeaderMeComp : NrResponseHeaderMeComp
  massActionReportId : BitVec 64
  deriving DecidableEq, Repr

namespace DeleteAllOrderNrResponse

def encode (message : DeleteAllOrderNrResponse) : List UInt8 :=
  Alpha.encode message.filler4
    ++ (NrResponseHeaderMeComp.encode message.nrResponseHeaderMeComp
    ++ (encodeUIntLE 8 message.massActionReportId))

def decode (bytes : List UInt8) : Option (DeleteAllOrderNrResponse × List UInt8) := do
  let (filler4, bytes) ← Alpha.decode 2 bytes
  let (nrResponseHeaderMeComp, bytes) ← NrResponseHeaderMeComp.decode bytes
  let (massActionReportId, bytes) ← decodeUIntLE 8 bytes
  pure ({ filler4, nrResponseHeaderMeComp, massActionReportId }, bytes)

@[simp] theorem encode_length (message : DeleteAllOrderNrResponse) : (encode message).length = 66 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, NrResponseHeaderMeComp.encode_length, encodeUIntLE_length]

theorem encode_length_pos (message : DeleteAllOrderNrResponse) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : DeleteAllOrderNrResponse) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, NrResponseHeaderMeComp.decode_encode, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : DeleteAllOrderNrResponse) : decode (encode message) = some (message, []) :=
  List.append_nil (encode message) ▸ decode_encode message []

end DeleteAllOrderNrResponse

/-- Delete All Order Quote Event Broadcast: 74 bytes -/
structure DeleteAllOrderQuoteEventBroadcast where
  filler4 : Alpha 2
  rbcHeaderMeComp : RbcHeaderMeComp
  massActionReportId : BitVec 64
  securityId : BitVec 64
  marketSegmentId : BitVec 32
  massActionReason : BitVec 8
  execInst : BitVec 8
  pad2 : Alpha 2
  deriving DecidableEq, Repr

namespace DeleteAllOrderQuoteEventBroadcast

def encode (message : DeleteAllOrderQuoteEventBroadcast) : List UInt8 :=
  Alpha.encode message.filler4
    ++ (RbcHeaderMeComp.encode message.rbcHeaderMeComp
    ++ (encodeUIntLE 8 message.massActionReportId
    ++ (encodeUIntLE 8 message.securityId
    ++ (encodeUIntLE 4 message.marketSegmentId
    ++ (encodeUInt 1 message.massActionReason
    ++ (encodeUInt 1 message.execInst
    ++ (Alpha.encode message.pad2)))))))

def decode (bytes : List UInt8) : Option (DeleteAllOrderQuoteEventBroadcast × List UInt8) := do
  let (filler4, bytes) ← Alpha.decode 2 bytes
  let (rbcHeaderMeComp, bytes) ← RbcHeaderMeComp.decode bytes
  let (massActionReportId, bytes) ← decodeUIntLE 8 bytes
  let (securityId, bytes) ← decodeUIntLE 8 bytes
  let (marketSegmentId, bytes) ← decodeUIntLE 4 bytes
  let (massActionReason, bytes) ← decodeUInt 1 bytes
  let (execInst, bytes) ← decodeUInt 1 bytes
  let (pad2, bytes) ← Alpha.decode 2 bytes
  pure ({ filler4, rbcHeaderMeComp, massActionReportId, securityId, marketSegmentId, massActionReason, execInst, pad2 }, bytes)

@[simp] theorem encode_length (message : DeleteAllOrderQuoteEventBroadcast) : (encode message).length = 74 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, RbcHeaderMeComp.encode_length, encodeUIntLE_length, encodeUInt_length]

theorem encode_length_pos (message : DeleteAllOrderQuoteEventBroadcast) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : DeleteAllOrderQuoteEventBroadcast) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, RbcHeaderMeComp.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : DeleteAllOrderQuoteEventBroadcast) : decode (encode message) = some (message, []) :=
  List.append_nil (encode message) ▸ decode_encode message []

end DeleteAllOrderQuoteEventBroadcast

/-- Response Header Me Comp: 72 bytes -/
structure ResponseHeaderMeComp where
  requestTime : BitVec 64
  requestOut : BitVec 64
  trdRegTsTimeIn : BitVec 64
  trdRegTsTimeOut : BitVec 64
  responseIn : BitVec 64
  sendingTime : BitVec 64
  msgSeqNum : BitVec 32
  partitionId : BitVec 16
  applId : BitVec 8
  applMsgId : Alpha 16
  lastFragment : BitVec 8
  deriving DecidableEq, Repr

namespace ResponseHeaderMeComp

def encode (message : ResponseHeaderMeComp) : List UInt8 :=
  encodeUIntLE 8 message.requestTime
    ++ (encodeUIntLE 8 message.requestOut
    ++ (encodeUIntLE 8 message.trdRegTsTimeIn
    ++ (encodeUIntLE 8 message.trdRegTsTimeOut
    ++ (encodeUIntLE 8 message.responseIn
    ++ (encodeUIntLE 8 message.sendingTime
    ++ (encodeUIntLE 4 message.msgSeqNum
    ++ (encodeUIntLE 2 message.partitionId
    ++ (encodeUInt 1 message.applId
    ++ (Alpha.encode message.applMsgId
    ++ (encodeUInt 1 message.lastFragment))))))))))

def decode (bytes : List UInt8) : Option (ResponseHeaderMeComp × List UInt8) := do
  let (requestTime, bytes) ← decodeUIntLE 8 bytes
  let (requestOut, bytes) ← decodeUIntLE 8 bytes
  let (trdRegTsTimeIn, bytes) ← decodeUIntLE 8 bytes
  let (trdRegTsTimeOut, bytes) ← decodeUIntLE 8 bytes
  let (responseIn, bytes) ← decodeUIntLE 8 bytes
  let (sendingTime, bytes) ← decodeUIntLE 8 bytes
  let (msgSeqNum, bytes) ← decodeUIntLE 4 bytes
  let (partitionId, bytes) ← decodeUIntLE 2 bytes
  let (applId, bytes) ← decodeUInt 1 bytes
  let (applMsgId, bytes) ← Alpha.decode 16 bytes
  let (lastFragment, bytes) ← decodeUInt 1 bytes
  pure ({ requestTime, requestOut, trdRegTsTimeIn, trdRegTsTimeOut, responseIn, sendingTime, msgSeqNum, partitionId, applId, applMsgId, lastFragment }, bytes)

@[simp] theorem encode_length (message : ResponseHeaderMeComp) : (encode message).length = 72 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, encodeUInt_length, Alpha.encode_length]

theorem encode_length_pos (message : ResponseHeaderMeComp) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : ResponseHeaderMeComp) (rest : List UInt8) :
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
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end ResponseHeaderMeComp

/-- Delete All Order Response -/
structure DeleteAllOrderResponse where
  filler4 : Alpha 2
  responseHeaderMeComp : ResponseHeaderMeComp
  massActionReportId : BitVec 64
  pad6 : Alpha 6
  notAffectedOrdersGrpComp : Bounded 2 NotAffectedOrdersGrpComp
  deriving DecidableEq, Repr

namespace DeleteAllOrderResponse

def encode (message : DeleteAllOrderResponse) : List UInt8 :=
  Alpha.encode message.filler4
    ++ (ResponseHeaderMeComp.encode message.responseHeaderMeComp
    ++ (encodeUIntLE 8 message.massActionReportId
    ++ (encodeUIntLE 2 (BitVec.ofNat (8 * 2) message.notAffectedOrdersGrpComp.val.length)
    ++ (Alpha.encode message.pad6
    ++ (encodeMany NotAffectedOrdersGrpComp.encode message.notAffectedOrdersGrpComp.val)))))

def decode (bytes : List UInt8) : Option (DeleteAllOrderResponse × List UInt8) := do
  let (filler4, bytes) ← Alpha.decode 2 bytes
  let (responseHeaderMeComp, bytes) ← ResponseHeaderMeComp.decode bytes
  let (massActionReportId, bytes) ← decodeUIntLE 8 bytes
  let (noNotAffectedOrders, bytes) ← decodeUIntLE 2 bytes
  let (pad6, bytes) ← Alpha.decode 6 bytes
  let (notAffectedOrdersGrpComp_, bytes) ← decodeMany NotAffectedOrdersGrpComp.decode noNotAffectedOrders.toNat bytes
  if fits_notAffectedOrdersGrpComp : notAffectedOrdersGrpComp_.length < 256 ^ 2 then
    pure ({ filler4, responseHeaderMeComp, massActionReportId, pad6, notAffectedOrdersGrpComp := ⟨notAffectedOrdersGrpComp_, fits_notAffectedOrdersGrpComp⟩ }, bytes)
  else none

theorem encode_length_pos (message : DeleteAllOrderResponse) : (encode message).length > 0 := by
  unfold encode
  simp only [Alpha.encode_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : DeleteAllOrderResponse) : (encode message).length ≤ 1048650 := by
  have bound_notAffectedOrdersGrpComp := message.notAffectedOrdersGrpComp.length_lt
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, Alpha.encode_length, ResponseHeaderMeComp.encode_length, encodeUIntLE_length, encodeMany_length_const NotAffectedOrdersGrpComp.encode 16 NotAffectedOrdersGrpComp.encode_length]
  omega

@[simp] theorem decode_encode (message : DeleteAllOrderResponse) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, ResponseHeaderMeComp.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [decodeMany_bounded 2 NotAffectedOrdersGrpComp.encode NotAffectedOrdersGrpComp.decode NotAffectedOrdersGrpComp.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.notAffectedOrdersGrpComp.length_lt]
  rfl

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : DeleteAllOrderResponse) : decode (encode message) = some (message, []) :=
  List.append_nil (encode message) ▸ decode_encode message []

end DeleteAllOrderResponse

/-- Not Affected Securities Grp Comp: 8 bytes -/
structure NotAffectedSecuritiesGrpComp where
  notAffectedSecurityId : BitVec 64
  deriving DecidableEq, Repr

namespace NotAffectedSecuritiesGrpComp

def encode (message : NotAffectedSecuritiesGrpComp) : List UInt8 :=
  encodeUIntLE 8 message.notAffectedSecurityId

def decode (bytes : List UInt8) : Option (NotAffectedSecuritiesGrpComp × List UInt8) := do
  let (notAffectedSecurityId, bytes) ← decodeUIntLE 8 bytes
  pure ({ notAffectedSecurityId }, bytes)

@[simp] theorem encode_length (message : NotAffectedSecuritiesGrpComp) : (encode message).length = 8 := by
  unfold encode
  simp only [encodeUIntLE_length]

theorem encode_length_pos (message : NotAffectedSecuritiesGrpComp) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : NotAffectedSecuritiesGrpComp) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end NotAffectedSecuritiesGrpComp

/-- Delete All Quote Broadcast -/
structure DeleteAllQuoteBroadcast where
  filler4 : Alpha 2
  rbcHeaderMeComp : RbcHeaderMeComp
  massActionReportId : BitVec 64
  securityId : BitVec 64
  marketSegmentId : BitVec 32
  targetPartyIdSessionId : BitVec 32
  partyIdEnteringTrader : BitVec 32
  targetPartyIdExecutingTrader : BitVec 32
  algoId : Alpha 16
  filler1 : Alpha 8
  filler2 : Alpha 4
  filler3 : Alpha 4
  massActionReason : BitVec 8
  partyIdEnteringFirm : BitVec 8
  targetPartyIdDeskId : Alpha 3
  pad1 : Alpha 1
  notAffectedSecuritiesGrpComp : Bounded 2 NotAffectedSecuritiesGrpComp
  deriving DecidableEq, Repr

namespace DeleteAllQuoteBroadcast

def encode (message : DeleteAllQuoteBroadcast) : List UInt8 :=
  Alpha.encode message.filler4
    ++ (RbcHeaderMeComp.encode message.rbcHeaderMeComp
    ++ (encodeUIntLE 8 message.massActionReportId
    ++ (encodeUIntLE 8 message.securityId
    ++ (encodeUIntLE 4 message.marketSegmentId
    ++ (encodeUIntLE 4 message.targetPartyIdSessionId
    ++ (encodeUIntLE 4 message.partyIdEnteringTrader
    ++ (encodeUIntLE 4 message.targetPartyIdExecutingTrader
    ++ (Alpha.encode message.algoId
    ++ (Alpha.encode message.filler1
    ++ (Alpha.encode message.filler2
    ++ (Alpha.encode message.filler3
    ++ (encodeUIntLE 2 (BitVec.ofNat (8 * 2) message.notAffectedSecuritiesGrpComp.val.length)
    ++ (encodeUInt 1 message.massActionReason
    ++ (encodeUInt 1 message.partyIdEnteringFirm
    ++ (Alpha.encode message.targetPartyIdDeskId
    ++ (Alpha.encode message.pad1
    ++ (encodeMany NotAffectedSecuritiesGrpComp.encode message.notAffectedSecuritiesGrpComp.val)))))))))))))))))

def decode (bytes : List UInt8) : Option (DeleteAllQuoteBroadcast × List UInt8) := do
  let (filler4, bytes) ← Alpha.decode 2 bytes
  let (rbcHeaderMeComp, bytes) ← RbcHeaderMeComp.decode bytes
  let (massActionReportId, bytes) ← decodeUIntLE 8 bytes
  let (securityId, bytes) ← decodeUIntLE 8 bytes
  let (marketSegmentId, bytes) ← decodeUIntLE 4 bytes
  let (targetPartyIdSessionId, bytes) ← decodeUIntLE 4 bytes
  let (partyIdEnteringTrader, bytes) ← decodeUIntLE 4 bytes
  let (targetPartyIdExecutingTrader, bytes) ← decodeUIntLE 4 bytes
  let (algoId, bytes) ← Alpha.decode 16 bytes
  let (filler1, bytes) ← Alpha.decode 8 bytes
  let (filler2, bytes) ← Alpha.decode 4 bytes
  let (filler3, bytes) ← Alpha.decode 4 bytes
  let (noNotAffectedSecurities, bytes) ← decodeUIntLE 2 bytes
  let (massActionReason, bytes) ← decodeUInt 1 bytes
  let (partyIdEnteringFirm, bytes) ← decodeUInt 1 bytes
  let (targetPartyIdDeskId, bytes) ← Alpha.decode 3 bytes
  let (pad1, bytes) ← Alpha.decode 1 bytes
  let (notAffectedSecuritiesGrpComp_, bytes) ← decodeMany NotAffectedSecuritiesGrpComp.decode noNotAffectedSecurities.toNat bytes
  if fits_notAffectedSecuritiesGrpComp : notAffectedSecuritiesGrpComp_.length < 256 ^ 2 then
    pure ({ filler4, rbcHeaderMeComp, massActionReportId, securityId, marketSegmentId, targetPartyIdSessionId, partyIdEnteringTrader, targetPartyIdExecutingTrader, algoId, filler1, filler2, filler3, massActionReason, partyIdEnteringFirm, targetPartyIdDeskId, pad1, notAffectedSecuritiesGrpComp := ⟨notAffectedSecuritiesGrpComp_, fits_notAffectedSecuritiesGrpComp⟩ }, bytes)
  else none

theorem encode_length_pos (message : DeleteAllQuoteBroadcast) : (encode message).length > 0 := by
  unfold encode
  simp only [Alpha.encode_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : DeleteAllQuoteBroadcast) : (encode message).length ≤ 524402 := by
  have bound_notAffectedSecuritiesGrpComp := message.notAffectedSecuritiesGrpComp.length_lt
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, Alpha.encode_length, RbcHeaderMeComp.encode_length, encodeUIntLE_length, encodeUInt_length, encodeMany_length_const NotAffectedSecuritiesGrpComp.encode 8 NotAffectedSecuritiesGrpComp.encode_length]
  omega

@[simp] theorem decode_encode (message : DeleteAllQuoteBroadcast) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, RbcHeaderMeComp.decode_encode, some_bind]
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
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [decodeMany_bounded 2 NotAffectedSecuritiesGrpComp.encode NotAffectedSecuritiesGrpComp.decode NotAffectedSecuritiesGrpComp.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.notAffectedSecuritiesGrpComp.length_lt]
  rfl

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : DeleteAllQuoteBroadcast) : decode (encode message) = some (message, []) :=
  List.append_nil (encode message) ▸ decode_encode message []

end DeleteAllQuoteBroadcast

/-- Delete All Quote Response -/
structure DeleteAllQuoteResponse where
  filler4 : Alpha 2
  nrResponseHeaderMeComp : NrResponseHeaderMeComp
  massActionReportId : BitVec 64
  pad6 : Alpha 6
  notAffectedSecuritiesGrpComp : Bounded 2 NotAffectedSecuritiesGrpComp
  deriving DecidableEq, Repr

namespace DeleteAllQuoteResponse

def encode (message : DeleteAllQuoteResponse) : List UInt8 :=
  Alpha.encode message.filler4
    ++ (NrResponseHeaderMeComp.encode message.nrResponseHeaderMeComp
    ++ (encodeUIntLE 8 message.massActionReportId
    ++ (encodeUIntLE 2 (BitVec.ofNat (8 * 2) message.notAffectedSecuritiesGrpComp.val.length)
    ++ (Alpha.encode message.pad6
    ++ (encodeMany NotAffectedSecuritiesGrpComp.encode message.notAffectedSecuritiesGrpComp.val)))))

def decode (bytes : List UInt8) : Option (DeleteAllQuoteResponse × List UInt8) := do
  let (filler4, bytes) ← Alpha.decode 2 bytes
  let (nrResponseHeaderMeComp, bytes) ← NrResponseHeaderMeComp.decode bytes
  let (massActionReportId, bytes) ← decodeUIntLE 8 bytes
  let (noNotAffectedSecurities, bytes) ← decodeUIntLE 2 bytes
  let (pad6, bytes) ← Alpha.decode 6 bytes
  let (notAffectedSecuritiesGrpComp_, bytes) ← decodeMany NotAffectedSecuritiesGrpComp.decode noNotAffectedSecurities.toNat bytes
  if fits_notAffectedSecuritiesGrpComp : notAffectedSecuritiesGrpComp_.length < 256 ^ 2 then
    pure ({ filler4, nrResponseHeaderMeComp, massActionReportId, pad6, notAffectedSecuritiesGrpComp := ⟨notAffectedSecuritiesGrpComp_, fits_notAffectedSecuritiesGrpComp⟩ }, bytes)
  else none

theorem encode_length_pos (message : DeleteAllQuoteResponse) : (encode message).length > 0 := by
  unfold encode
  simp only [Alpha.encode_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : DeleteAllQuoteResponse) : (encode message).length ≤ 524354 := by
  have bound_notAffectedSecuritiesGrpComp := message.notAffectedSecuritiesGrpComp.length_lt
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, Alpha.encode_length, NrResponseHeaderMeComp.encode_length, encodeUIntLE_length, encodeMany_length_const NotAffectedSecuritiesGrpComp.encode 8 NotAffectedSecuritiesGrpComp.encode_length]
  omega

@[simp] theorem decode_encode (message : DeleteAllQuoteResponse) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, NrResponseHeaderMeComp.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [decodeMany_bounded 2 NotAffectedSecuritiesGrpComp.encode NotAffectedSecuritiesGrpComp.decode NotAffectedSecuritiesGrpComp.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.notAffectedSecuritiesGrpComp.length_lt]
  rfl

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : DeleteAllQuoteResponse) : decode (encode message) = some (message, []) :=
  List.append_nil (encode message) ▸ decode_encode message []

end DeleteAllQuoteResponse

/-- Delete Order Broadcast: 122 bytes -/
structure DeleteOrderBroadcast where
  filler4 : Alpha 2
  rbcHeaderMeComp : RbcHeaderMeComp
  orderId : BitVec 64
  clOrdId : BitVec 64
  origClOrdId : BitVec 64
  securityId : BitVec 64
  execId : BitVec 64
  messageTag : BitVec 32
  cumQty : BitVec 32
  cxlQty : BitVec 32
  marketSegmentId : BitVec 32
  partyIdEnteringTrader : BitVec 32
  execRestatementReason : BitVec 16
  partyIdEnteringFirm : BitVec 8
  ordStatus : OrdStatus
  execType : ExecType
  productComplex : BitVec 8
  side : BitVec 8
  pad5 : Alpha 5
  deriving DecidableEq, Repr

namespace DeleteOrderBroadcast

def encode (message : DeleteOrderBroadcast) : List UInt8 :=
  Alpha.encode message.filler4
    ++ (RbcHeaderMeComp.encode message.rbcHeaderMeComp
    ++ (encodeUIntLE 8 message.orderId
    ++ (encodeUIntLE 8 message.clOrdId
    ++ (encodeUIntLE 8 message.origClOrdId
    ++ (encodeUIntLE 8 message.securityId
    ++ (encodeUIntLE 8 message.execId
    ++ (encodeUIntLE 4 message.messageTag
    ++ (encodeUIntLE 4 message.cumQty
    ++ (encodeUIntLE 4 message.cxlQty
    ++ (encodeUIntLE 4 message.marketSegmentId
    ++ (encodeUIntLE 4 message.partyIdEnteringTrader
    ++ (encodeUIntLE 2 message.execRestatementReason
    ++ (encodeUInt 1 message.partyIdEnteringFirm
    ++ (OrdStatus.encode message.ordStatus
    ++ (ExecType.encode message.execType
    ++ (encodeUInt 1 message.productComplex
    ++ (encodeUInt 1 message.side
    ++ (Alpha.encode message.pad5))))))))))))))))))

def decode (bytes : List UInt8) : Option (DeleteOrderBroadcast × List UInt8) := do
  let (filler4, bytes) ← Alpha.decode 2 bytes
  let (rbcHeaderMeComp, bytes) ← RbcHeaderMeComp.decode bytes
  let (orderId, bytes) ← decodeUIntLE 8 bytes
  let (clOrdId, bytes) ← decodeUIntLE 8 bytes
  let (origClOrdId, bytes) ← decodeUIntLE 8 bytes
  let (securityId, bytes) ← decodeUIntLE 8 bytes
  let (execId, bytes) ← decodeUIntLE 8 bytes
  let (messageTag, bytes) ← decodeUIntLE 4 bytes
  let (cumQty, bytes) ← decodeUIntLE 4 bytes
  let (cxlQty, bytes) ← decodeUIntLE 4 bytes
  let (marketSegmentId, bytes) ← decodeUIntLE 4 bytes
  let (partyIdEnteringTrader, bytes) ← decodeUIntLE 4 bytes
  let (execRestatementReason, bytes) ← decodeUIntLE 2 bytes
  let (partyIdEnteringFirm, bytes) ← decodeUInt 1 bytes
  let (ordStatus, bytes) ← OrdStatus.decode bytes
  let (execType, bytes) ← ExecType.decode bytes
  let (productComplex, bytes) ← decodeUInt 1 bytes
  let (side, bytes) ← decodeUInt 1 bytes
  let (pad5, bytes) ← Alpha.decode 5 bytes
  pure ({ filler4, rbcHeaderMeComp, orderId, clOrdId, origClOrdId, securityId, execId, messageTag, cumQty, cxlQty, marketSegmentId, partyIdEnteringTrader, execRestatementReason, partyIdEnteringFirm, ordStatus, execType, productComplex, side, pad5 }, bytes)

@[simp] theorem encode_length (message : DeleteOrderBroadcast) : (encode message).length = 122 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, RbcHeaderMeComp.encode_length, encodeUIntLE_length, encodeUInt_length, OrdStatus.encode_length, ExecType.encode_length]

theorem encode_length_pos (message : DeleteOrderBroadcast) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : DeleteOrderBroadcast) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, RbcHeaderMeComp.decode_encode, some_bind]
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
  rw [Alpha.decode_encode, some_bind]
  rfl

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : DeleteOrderBroadcast) : decode (encode message) = some (message, []) :=
  List.append_nil (encode message) ▸ decode_encode message []

end DeleteOrderBroadcast

/-- Delete Order Nr Response: 114 bytes -/
structure DeleteOrderNrResponse where
  filler4 : Alpha 2
  nrResponseHeaderMeComp : NrResponseHeaderMeComp
  orderId : BitVec 64
  clOrdId : BitVec 64
  origClOrdId : BitVec 64
  securityId : BitVec 64
  execId : BitVec 64
  cumQty : BitVec 32
  cxlQty : BitVec 32
  ordStatus : OrdStatus
  execType : ExecType
  execRestatementReason : BitVec 16
  productComplex : BitVec 8
  pad3 : Alpha 3
  deriving DecidableEq, Repr

namespace DeleteOrderNrResponse

def encode (message : DeleteOrderNrResponse) : List UInt8 :=
  Alpha.encode message.filler4
    ++ (NrResponseHeaderMeComp.encode message.nrResponseHeaderMeComp
    ++ (encodeUIntLE 8 message.orderId
    ++ (encodeUIntLE 8 message.clOrdId
    ++ (encodeUIntLE 8 message.origClOrdId
    ++ (encodeUIntLE 8 message.securityId
    ++ (encodeUIntLE 8 message.execId
    ++ (encodeUIntLE 4 message.cumQty
    ++ (encodeUIntLE 4 message.cxlQty
    ++ (OrdStatus.encode message.ordStatus
    ++ (ExecType.encode message.execType
    ++ (encodeUIntLE 2 message.execRestatementReason
    ++ (encodeUInt 1 message.productComplex
    ++ (Alpha.encode message.pad3)))))))))))))

def decode (bytes : List UInt8) : Option (DeleteOrderNrResponse × List UInt8) := do
  let (filler4, bytes) ← Alpha.decode 2 bytes
  let (nrResponseHeaderMeComp, bytes) ← NrResponseHeaderMeComp.decode bytes
  let (orderId, bytes) ← decodeUIntLE 8 bytes
  let (clOrdId, bytes) ← decodeUIntLE 8 bytes
  let (origClOrdId, bytes) ← decodeUIntLE 8 bytes
  let (securityId, bytes) ← decodeUIntLE 8 bytes
  let (execId, bytes) ← decodeUIntLE 8 bytes
  let (cumQty, bytes) ← decodeUIntLE 4 bytes
  let (cxlQty, bytes) ← decodeUIntLE 4 bytes
  let (ordStatus, bytes) ← OrdStatus.decode bytes
  let (execType, bytes) ← ExecType.decode bytes
  let (execRestatementReason, bytes) ← decodeUIntLE 2 bytes
  let (productComplex, bytes) ← decodeUInt 1 bytes
  let (pad3, bytes) ← Alpha.decode 3 bytes
  pure ({ filler4, nrResponseHeaderMeComp, orderId, clOrdId, origClOrdId, securityId, execId, cumQty, cxlQty, ordStatus, execType, execRestatementReason, productComplex, pad3 }, bytes)

@[simp] theorem encode_length (message : DeleteOrderNrResponse) : (encode message).length = 114 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, NrResponseHeaderMeComp.encode_length, encodeUIntLE_length, OrdStatus.encode_length, ExecType.encode_length, encodeUInt_length]

theorem encode_length_pos (message : DeleteOrderNrResponse) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : DeleteOrderNrResponse) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, NrResponseHeaderMeComp.decode_encode, some_bind]
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
  rw [List.append_assoc, OrdStatus.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, ExecType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : DeleteOrderNrResponse) : decode (encode message) = some (message, []) :=
  List.append_nil (encode message) ▸ decode_encode message []

end DeleteOrderNrResponse

/-- Delete Order Response: 130 bytes -/
structure DeleteOrderResponse where
  filler4 : Alpha 2
  responseHeaderMeComp : ResponseHeaderMeComp
  orderId : BitVec 64
  clOrdId : BitVec 64
  origClOrdId : BitVec 64
  securityId : BitVec 64
  execId : BitVec 64
  cumQty : BitVec 32
  cxlQty : BitVec 32
  ordStatus : OrdStatus
  execType : ExecType
  execRestatementReason : BitVec 16
  productComplex : BitVec 8
  pad3 : Alpha 3
  deriving DecidableEq, Repr

namespace DeleteOrderResponse

def encode (message : DeleteOrderResponse) : List UInt8 :=
  Alpha.encode message.filler4
    ++ (ResponseHeaderMeComp.encode message.responseHeaderMeComp
    ++ (encodeUIntLE 8 message.orderId
    ++ (encodeUIntLE 8 message.clOrdId
    ++ (encodeUIntLE 8 message.origClOrdId
    ++ (encodeUIntLE 8 message.securityId
    ++ (encodeUIntLE 8 message.execId
    ++ (encodeUIntLE 4 message.cumQty
    ++ (encodeUIntLE 4 message.cxlQty
    ++ (OrdStatus.encode message.ordStatus
    ++ (ExecType.encode message.execType
    ++ (encodeUIntLE 2 message.execRestatementReason
    ++ (encodeUInt 1 message.productComplex
    ++ (Alpha.encode message.pad3)))))))))))))

def decode (bytes : List UInt8) : Option (DeleteOrderResponse × List UInt8) := do
  let (filler4, bytes) ← Alpha.decode 2 bytes
  let (responseHeaderMeComp, bytes) ← ResponseHeaderMeComp.decode bytes
  let (orderId, bytes) ← decodeUIntLE 8 bytes
  let (clOrdId, bytes) ← decodeUIntLE 8 bytes
  let (origClOrdId, bytes) ← decodeUIntLE 8 bytes
  let (securityId, bytes) ← decodeUIntLE 8 bytes
  let (execId, bytes) ← decodeUIntLE 8 bytes
  let (cumQty, bytes) ← decodeUIntLE 4 bytes
  let (cxlQty, bytes) ← decodeUIntLE 4 bytes
  let (ordStatus, bytes) ← OrdStatus.decode bytes
  let (execType, bytes) ← ExecType.decode bytes
  let (execRestatementReason, bytes) ← decodeUIntLE 2 bytes
  let (productComplex, bytes) ← decodeUInt 1 bytes
  let (pad3, bytes) ← Alpha.decode 3 bytes
  pure ({ filler4, responseHeaderMeComp, orderId, clOrdId, origClOrdId, securityId, execId, cumQty, cxlQty, ordStatus, execType, execRestatementReason, productComplex, pad3 }, bytes)

@[simp] theorem encode_length (message : DeleteOrderResponse) : (encode message).length = 130 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, ResponseHeaderMeComp.encode_length, encodeUIntLE_length, OrdStatus.encode_length, ExecType.encode_length, encodeUInt_length]

theorem encode_length_pos (message : DeleteOrderResponse) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : DeleteOrderResponse) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, ResponseHeaderMeComp.decode_encode, some_bind]
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
  rw [List.append_assoc, OrdStatus.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, ExecType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : DeleteOrderResponse) : decode (encode message) = some (message, []) :=
  List.append_nil (encode message) ▸ decode_encode message []

end DeleteOrderResponse

/-- Forced Logout Notification -/
structure ForcedLogoutNotification where
  filler4 : Alpha 2
  notifHeaderComp : NotifHeaderComp
  pad6 : Alpha 6
  varText : Bounded 2 UInt8
  alignmentPadding : Capped 7
  deriving DecidableEq, Repr

namespace ForcedLogoutNotification

def encode (message : ForcedLogoutNotification) : List UInt8 :=
  Alpha.encode message.filler4
    ++ (NotifHeaderComp.encode message.notifHeaderComp
    ++ (encodeUIntLE 2 (BitVec.ofNat (8 * 2) message.varText.val.length)
    ++ (Alpha.encode message.pad6
    ++ (encodeMany Byte.encode message.varText.val
    ++ (message.alignmentPadding.val)))))

def decode (bytes : List UInt8) : Option ForcedLogoutNotification := do
  let (filler4, bytes) ← Alpha.decode 2 bytes
  let (notifHeaderComp, bytes) ← NotifHeaderComp.decode bytes
  let (varTextLen, bytes) ← decodeUIntLE 2 bytes
  let (pad6, bytes) ← Alpha.decode 6 bytes
  let (varText_, bytes) ← decodeMany Byte.decode varTextLen.toNat bytes
  let alignmentPadding_ := bytes
  if fits_varText : varText_.length < 256 ^ 2 then
    if fits_alignmentPadding : alignmentPadding_.length ≤ 7 then
      pure { filler4, notifHeaderComp, pad6, varText := ⟨varText_, fits_varText⟩, alignmentPadding := ⟨alignmentPadding_, fits_alignmentPadding⟩ }
    else none
  else none

theorem encode_length_pos (message : ForcedLogoutNotification) : (encode message).length > 0 := by
  unfold encode
  simp only [Alpha.encode_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : ForcedLogoutNotification) : (encode message).length ≤ 65560 := by
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
  rw [Alpha.decode_encode, some_bind]
  dsimp only
  rw [decodeMany_bounded 2 Byte.encode Byte.decode Byte.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.varText.length_lt, dite_eq_left message.alignmentPadding.length_le]
  rfl

end ForcedLogoutNotification

/-- Response Header Comp: 24 bytes -/
structure ResponseHeaderComp where
  requestTime : BitVec 64
  sendingTime : BitVec 64
  msgSeqNum : BitVec 32
  pad4 : Alpha 4
  deriving DecidableEq, Repr

namespace ResponseHeaderComp

def encode (message : ResponseHeaderComp) : List UInt8 :=
  encodeUIntLE 8 message.requestTime
    ++ (encodeUIntLE 8 message.sendingTime
    ++ (encodeUIntLE 4 message.msgSeqNum
    ++ (Alpha.encode message.pad4)))

def decode (bytes : List UInt8) : Option (ResponseHeaderComp × List UInt8) := do
  let (requestTime, bytes) ← decodeUIntLE 8 bytes
  let (sendingTime, bytes) ← decodeUIntLE 8 bytes
  let (msgSeqNum, bytes) ← decodeUIntLE 4 bytes
  let (pad4, bytes) ← Alpha.decode 4 bytes
  pure ({ requestTime, sendingTime, msgSeqNum, pad4 }, bytes)

@[simp] theorem encode_length (message : ResponseHeaderComp) : (encode message).length = 24 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length]

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
  rw [Alpha.decode_encode, some_bind]
  rfl

end ResponseHeaderComp

/-- Gateway Response: 98 bytes -/
structure GatewayResponse where
  filler4 : Alpha 2
  responseHeaderComp : ResponseHeaderComp
  gatewayId : BitVec 32
  gatewaySubId : BitVec 32
  secondaryGatewayId : BitVec 32
  secondaryGatewaySubId : BitVec 32
  sessionMode : BitVec 8
  tradSesMode : BitVec 8
  securityKey : Alpha 32
  initializationVector : Alpha 16
  pad6 : Alpha 6
  deriving DecidableEq, Repr

namespace GatewayResponse

def encode (message : GatewayResponse) : List UInt8 :=
  Alpha.encode message.filler4
    ++ (ResponseHeaderComp.encode message.responseHeaderComp
    ++ (encodeUIntLE 4 message.gatewayId
    ++ (encodeUIntLE 4 message.gatewaySubId
    ++ (encodeUIntLE 4 message.secondaryGatewayId
    ++ (encodeUIntLE 4 message.secondaryGatewaySubId
    ++ (encodeUInt 1 message.sessionMode
    ++ (encodeUInt 1 message.tradSesMode
    ++ (Alpha.encode message.securityKey
    ++ (Alpha.encode message.initializationVector
    ++ (Alpha.encode message.pad6))))))))))

def decode (bytes : List UInt8) : Option (GatewayResponse × List UInt8) := do
  let (filler4, bytes) ← Alpha.decode 2 bytes
  let (responseHeaderComp, bytes) ← ResponseHeaderComp.decode bytes
  let (gatewayId, bytes) ← decodeUIntLE 4 bytes
  let (gatewaySubId, bytes) ← decodeUIntLE 4 bytes
  let (secondaryGatewayId, bytes) ← decodeUIntLE 4 bytes
  let (secondaryGatewaySubId, bytes) ← decodeUIntLE 4 bytes
  let (sessionMode, bytes) ← decodeUInt 1 bytes
  let (tradSesMode, bytes) ← decodeUInt 1 bytes
  let (securityKey, bytes) ← Alpha.decode 32 bytes
  let (initializationVector, bytes) ← Alpha.decode 16 bytes
  let (pad6, bytes) ← Alpha.decode 6 bytes
  pure ({ filler4, responseHeaderComp, gatewayId, gatewaySubId, secondaryGatewayId, secondaryGatewaySubId, sessionMode, tradSesMode, securityKey, initializationVector, pad6 }, bytes)

@[simp] theorem encode_length (message : GatewayResponse) : (encode message).length = 98 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, ResponseHeaderComp.encode_length, encodeUIntLE_length, encodeUInt_length]

theorem encode_length_pos (message : GatewayResponse) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : GatewayResponse) (rest : List UInt8) :
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
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
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
theorem decode_encode_nil (message : GatewayResponse) : decode (encode message) = some (message, []) :=
  List.append_nil (encode message) ▸ decode_encode message []

end GatewayResponse

/-- Gw Order Acknowledgement: 50 bytes -/
structure GwOrderAcknowledgement where
  filler4 : Alpha 2
  responseHeaderComp : ResponseHeaderComp
  primaryOrderId : BitVec 64
  clOrdId : BitVec 64
  messageTag : BitVec 32
  pad4 : Alpha 4
  deriving DecidableEq, Repr

namespace GwOrderAcknowledgement

def encode (message : GwOrderAcknowledgement) : List UInt8 :=
  Alpha.encode message.filler4
    ++ (ResponseHeaderComp.encode message.responseHeaderComp
    ++ (encodeUIntLE 8 message.primaryOrderId
    ++ (encodeUIntLE 8 message.clOrdId
    ++ (encodeUIntLE 4 message.messageTag
    ++ (Alpha.encode message.pad4)))))

def decode (bytes : List UInt8) : Option (GwOrderAcknowledgement × List UInt8) := do
  let (filler4, bytes) ← Alpha.decode 2 bytes
  let (responseHeaderComp, bytes) ← ResponseHeaderComp.decode bytes
  let (primaryOrderId, bytes) ← decodeUIntLE 8 bytes
  let (clOrdId, bytes) ← decodeUIntLE 8 bytes
  let (messageTag, bytes) ← decodeUIntLE 4 bytes
  let (pad4, bytes) ← Alpha.decode 4 bytes
  pure ({ filler4, responseHeaderComp, primaryOrderId, clOrdId, messageTag, pad4 }, bytes)

@[simp] theorem encode_length (message : GwOrderAcknowledgement) : (encode message).length = 50 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, ResponseHeaderComp.encode_length, encodeUIntLE_length]

theorem encode_length_pos (message : GwOrderAcknowledgement) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : GwOrderAcknowledgement) (rest : List UInt8) :
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
  rw [Alpha.decode_encode, some_bind]
  rfl

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : GwOrderAcknowledgement) : decode (encode message) = some (message, []) :=
  List.append_nil (encode message) ▸ decode_encode message []

end GwOrderAcknowledgement

/-- Heartbeat Notification: 10 bytes -/
structure HeartbeatNotification where
  filler4 : Alpha 2
  notifHeaderComp : NotifHeaderComp
  deriving DecidableEq, Repr

namespace HeartbeatNotification

def encode (message : HeartbeatNotification) : List UInt8 :=
  Alpha.encode message.filler4
    ++ (NotifHeaderComp.encode message.notifHeaderComp)

def decode (bytes : List UInt8) : Option (HeartbeatNotification × List UInt8) := do
  let (filler4, bytes) ← Alpha.decode 2 bytes
  let (notifHeaderComp, bytes) ← NotifHeaderComp.decode bytes
  pure ({ filler4, notifHeaderComp }, bytes)

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

/-- Sessions Grp Comp: 8 bytes -/
structure SessionsGrpComp where
  partyIdSessionId : BitVec 32
  sessionMode : BitVec 8
  sessionSubMode : BitVec 8
  pad2 : Alpha 2
  deriving DecidableEq, Repr

namespace SessionsGrpComp

def encode (message : SessionsGrpComp) : List UInt8 :=
  encodeUIntLE 4 message.partyIdSessionId
    ++ (encodeUInt 1 message.sessionMode
    ++ (encodeUInt 1 message.sessionSubMode
    ++ (Alpha.encode message.pad2)))

def decode (bytes : List UInt8) : Option (SessionsGrpComp × List UInt8) := do
  let (partyIdSessionId, bytes) ← decodeUIntLE 4 bytes
  let (sessionMode, bytes) ← decodeUInt 1 bytes
  let (sessionSubMode, bytes) ← decodeUInt 1 bytes
  let (pad2, bytes) ← Alpha.decode 2 bytes
  pure ({ partyIdSessionId, sessionMode, sessionSubMode, pad2 }, bytes)

@[simp] theorem encode_length (message : SessionsGrpComp) : (encode message).length = 8 := by
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
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end SessionsGrpComp

/-- Inquire Session List Response -/
structure InquireSessionListResponse where
  filler4 : Alpha 2
  responseHeaderComp : ResponseHeaderComp
  pad6 : Alpha 6
  sessionsGrpComp : Bounded 2 SessionsGrpComp
  deriving DecidableEq, Repr

namespace InquireSessionListResponse

def encode (message : InquireSessionListResponse) : List UInt8 :=
  Alpha.encode message.filler4
    ++ (ResponseHeaderComp.encode message.responseHeaderComp
    ++ (encodeUIntLE 2 (BitVec.ofNat (8 * 2) message.sessionsGrpComp.val.length)
    ++ (Alpha.encode message.pad6
    ++ (encodeMany SessionsGrpComp.encode message.sessionsGrpComp.val))))

def decode (bytes : List UInt8) : Option (InquireSessionListResponse × List UInt8) := do
  let (filler4, bytes) ← Alpha.decode 2 bytes
  let (responseHeaderComp, bytes) ← ResponseHeaderComp.decode bytes
  let (noSessions, bytes) ← decodeUIntLE 2 bytes
  let (pad6, bytes) ← Alpha.decode 6 bytes
  let (sessionsGrpComp_, bytes) ← decodeMany SessionsGrpComp.decode noSessions.toNat bytes
  if fits_sessionsGrpComp : sessionsGrpComp_.length < 256 ^ 2 then
    pure ({ filler4, responseHeaderComp, pad6, sessionsGrpComp := ⟨sessionsGrpComp_, fits_sessionsGrpComp⟩ }, bytes)
  else none

theorem encode_length_pos (message : InquireSessionListResponse) : (encode message).length > 0 := by
  unfold encode
  simp only [Alpha.encode_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : InquireSessionListResponse) : (encode message).length ≤ 524314 := by
  have bound_sessionsGrpComp := message.sessionsGrpComp.length_lt
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, Alpha.encode_length, ResponseHeaderComp.encode_length, encodeUIntLE_length, encodeMany_length_const SessionsGrpComp.encode 8 SessionsGrpComp.encode_length]
  omega

@[simp] theorem decode_encode (message : InquireSessionListResponse) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, ResponseHeaderComp.decode_encode, some_bind]
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
theorem decode_encode_nil (message : InquireSessionListResponse) : decode (encode message) = some (message, []) :=
  List.append_nil (encode message) ▸ decode_encode message []

end InquireSessionListResponse

/-- Logon Response: 98 bytes -/
structure LogonResponse where
  filler4 : Alpha 2
  responseHeaderComp : ResponseHeaderComp
  throttleTimeInterval : BitVec 64
  lastLoginTime : BitVec 64
  lastLoginIp : BitVec 32
  throttleNoMsgs : BitVec 32
  throttleDisconnectLimit : BitVec 32
  heartBtInt : BitVec 32
  sessionInstanceId : BitVec 32
  tradSesMode : BitVec 8
  noOfPartition : BitVec 8
  daysLeftForPasswdExpiry : BitVec 8
  graceLoginsLeft : BitVec 8
  defaultCstmApplVerId : Alpha 30
  pad2 : Alpha 2
  deriving DecidableEq, Repr

namespace LogonResponse

def encode (message : LogonResponse) : List UInt8 :=
  Alpha.encode message.filler4
    ++ (ResponseHeaderComp.encode message.responseHeaderComp
    ++ (encodeUIntLE 8 message.throttleTimeInterval
    ++ (encodeUIntLE 8 message.lastLoginTime
    ++ (encodeUIntLE 4 message.lastLoginIp
    ++ (encodeUIntLE 4 message.throttleNoMsgs
    ++ (encodeUIntLE 4 message.throttleDisconnectLimit
    ++ (encodeUIntLE 4 message.heartBtInt
    ++ (encodeUIntLE 4 message.sessionInstanceId
    ++ (encodeUInt 1 message.tradSesMode
    ++ (encodeUInt 1 message.noOfPartition
    ++ (encodeUInt 1 message.daysLeftForPasswdExpiry
    ++ (encodeUInt 1 message.graceLoginsLeft
    ++ (Alpha.encode message.defaultCstmApplVerId
    ++ (Alpha.encode message.pad2))))))))))))))

def decode (bytes : List UInt8) : Option (LogonResponse × List UInt8) := do
  let (filler4, bytes) ← Alpha.decode 2 bytes
  let (responseHeaderComp, bytes) ← ResponseHeaderComp.decode bytes
  let (throttleTimeInterval, bytes) ← decodeUIntLE 8 bytes
  let (lastLoginTime, bytes) ← decodeUIntLE 8 bytes
  let (lastLoginIp, bytes) ← decodeUIntLE 4 bytes
  let (throttleNoMsgs, bytes) ← decodeUIntLE 4 bytes
  let (throttleDisconnectLimit, bytes) ← decodeUIntLE 4 bytes
  let (heartBtInt, bytes) ← decodeUIntLE 4 bytes
  let (sessionInstanceId, bytes) ← decodeUIntLE 4 bytes
  let (tradSesMode, bytes) ← decodeUInt 1 bytes
  let (noOfPartition, bytes) ← decodeUInt 1 bytes
  let (daysLeftForPasswdExpiry, bytes) ← decodeUInt 1 bytes
  let (graceLoginsLeft, bytes) ← decodeUInt 1 bytes
  let (defaultCstmApplVerId, bytes) ← Alpha.decode 30 bytes
  let (pad2, bytes) ← Alpha.decode 2 bytes
  pure ({ filler4, responseHeaderComp, throttleTimeInterval, lastLoginTime, lastLoginIp, throttleNoMsgs, throttleDisconnectLimit, heartBtInt, sessionInstanceId, tradSesMode, noOfPartition, daysLeftForPasswdExpiry, graceLoginsLeft, defaultCstmApplVerId, pad2 }, bytes)

@[simp] theorem encode_length (message : LogonResponse) : (encode message).length = 98 := by
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
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
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
  filler4 : Alpha 2
  responseHeaderComp : ResponseHeaderComp
  deriving DecidableEq, Repr

namespace LogoutResponse

def encode (message : LogoutResponse) : List UInt8 :=
  Alpha.encode message.filler4
    ++ (ResponseHeaderComp.encode message.responseHeaderComp)

def decode (bytes : List UInt8) : Option (LogoutResponse × List UInt8) := do
  let (filler4, bytes) ← Alpha.decode 2 bytes
  let (responseHeaderComp, bytes) ← ResponseHeaderComp.decode bytes
  pure ({ filler4, responseHeaderComp }, bytes)

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

/-- Quote Entry Ack Grp Comp: 24 bytes -/
structure QuoteEntryAckGrpComp where
  securityId : BitVec 64
  bidCxlSize : BitVec 32
  offerCxlSize : BitVec 32
  quoteEntryRejectReason : BitVec 32
  quoteEntryStatus : BitVec 8
  pad3 : Alpha 3
  deriving DecidableEq, Repr

namespace QuoteEntryAckGrpComp

def encode (message : QuoteEntryAckGrpComp) : List UInt8 :=
  encodeUIntLE 8 message.securityId
    ++ (encodeUIntLE 4 message.bidCxlSize
    ++ (encodeUIntLE 4 message.offerCxlSize
    ++ (encodeUIntLE 4 message.quoteEntryRejectReason
    ++ (encodeUInt 1 message.quoteEntryStatus
    ++ (Alpha.encode message.pad3)))))

def decode (bytes : List UInt8) : Option (QuoteEntryAckGrpComp × List UInt8) := do
  let (securityId, bytes) ← decodeUIntLE 8 bytes
  let (bidCxlSize, bytes) ← decodeUIntLE 4 bytes
  let (offerCxlSize, bytes) ← decodeUIntLE 4 bytes
  let (quoteEntryRejectReason, bytes) ← decodeUIntLE 4 bytes
  let (quoteEntryStatus, bytes) ← decodeUInt 1 bytes
  let (pad3, bytes) ← Alpha.decode 3 bytes
  pure ({ securityId, bidCxlSize, offerCxlSize, quoteEntryRejectReason, quoteEntryStatus, pad3 }, bytes)

@[simp] theorem encode_length (message : QuoteEntryAckGrpComp) : (encode message).length = 24 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, encodeUInt_length, Alpha.encode_length]

theorem encode_length_pos (message : QuoteEntryAckGrpComp) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : QuoteEntryAckGrpComp) (rest : List UInt8) :
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
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end QuoteEntryAckGrpComp

/-- Mass Quote Response -/
structure MassQuoteResponse where
  filler4 : Alpha 2
  nrResponseHeaderMeComp : NrResponseHeaderMeComp
  quoteId : BitVec 64
  quoteResponseId : BitVec 64
  marketSegmentId : BitVec 32
  pad3 : Alpha 3
  quoteEntryAckGrpComp : Bounded 1 QuoteEntryAckGrpComp
  deriving DecidableEq, Repr

namespace MassQuoteResponse

def encode (message : MassQuoteResponse) : List UInt8 :=
  Alpha.encode message.filler4
    ++ (NrResponseHeaderMeComp.encode message.nrResponseHeaderMeComp
    ++ (encodeUIntLE 8 message.quoteId
    ++ (encodeUIntLE 8 message.quoteResponseId
    ++ (encodeUIntLE 4 message.marketSegmentId
    ++ (encodeUInt 1 (BitVec.ofNat (8 * 1) message.quoteEntryAckGrpComp.val.length)
    ++ (Alpha.encode message.pad3
    ++ (encodeMany QuoteEntryAckGrpComp.encode message.quoteEntryAckGrpComp.val)))))))

def decode (bytes : List UInt8) : Option (MassQuoteResponse × List UInt8) := do
  let (filler4, bytes) ← Alpha.decode 2 bytes
  let (nrResponseHeaderMeComp, bytes) ← NrResponseHeaderMeComp.decode bytes
  let (quoteId, bytes) ← decodeUIntLE 8 bytes
  let (quoteResponseId, bytes) ← decodeUIntLE 8 bytes
  let (marketSegmentId, bytes) ← decodeUIntLE 4 bytes
  let (noQuoteEntries, bytes) ← decodeUInt 1 bytes
  let (pad3, bytes) ← Alpha.decode 3 bytes
  let (quoteEntryAckGrpComp_, bytes) ← decodeMany QuoteEntryAckGrpComp.decode noQuoteEntries.toNat bytes
  if fits_quoteEntryAckGrpComp : quoteEntryAckGrpComp_.length < 256 ^ 1 then
    pure ({ filler4, nrResponseHeaderMeComp, quoteId, quoteResponseId, marketSegmentId, pad3, quoteEntryAckGrpComp := ⟨quoteEntryAckGrpComp_, fits_quoteEntryAckGrpComp⟩ }, bytes)
  else none

theorem encode_length_pos (message : MassQuoteResponse) : (encode message).length > 0 := by
  unfold encode
  simp only [Alpha.encode_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : MassQuoteResponse) : (encode message).length ≤ 6202 := by
  have bound_quoteEntryAckGrpComp := message.quoteEntryAckGrpComp.length_lt
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, Alpha.encode_length, NrResponseHeaderMeComp.encode_length, encodeUIntLE_length, encodeUInt_length, encodeMany_length_const QuoteEntryAckGrpComp.encode 24 QuoteEntryAckGrpComp.encode_length]
  omega

@[simp] theorem decode_encode (message : MassQuoteResponse) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, NrResponseHeaderMeComp.decode_encode, some_bind]
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
  rw [decodeMany_bounded 1 QuoteEntryAckGrpComp.encode QuoteEntryAckGrpComp.decode QuoteEntryAckGrpComp.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.quoteEntryAckGrpComp.length_lt]
  rfl

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : MassQuoteResponse) : decode (encode message) = some (message, []) :=
  List.append_nil (encode message) ▸ decode_encode message []

end MassQuoteResponse

/-- Modify Order Nr Response: 162 bytes -/
structure ModifyOrderNrResponse where
  filler4 : Alpha 2
  nrResponseHeaderMeComp : NrResponseHeaderMeComp
  orderId : BitVec 64
  clOrdId : BitVec 64
  origClOrdId : BitVec 64
  securityId : BitVec 64
  execId : BitVec 64
  priceMkToLimitPx : BitVec 64
  yield : BitVec 64
  underlyingDirtyPrice : BitVec 64
  activityTime : BitVec 64
  filler1 : Alpha 8
  filler2 : Alpha 4
  leavesQty : BitVec 32
  cumQty : BitVec 32
  cxlQty : BitVec 32
  filler4v2 : Alpha 2
  ordStatus : OrdStatus
  execType : ExecType
  execRestatementReason : BitVec 16
  productComplex : BitVec 8
  rolloverFlag : BitVec 8
  deriving DecidableEq, Repr

namespace ModifyOrderNrResponse

def encode (message : ModifyOrderNrResponse) : List UInt8 :=
  Alpha.encode message.filler4
    ++ (NrResponseHeaderMeComp.encode message.nrResponseHeaderMeComp
    ++ (encodeUIntLE 8 message.orderId
    ++ (encodeUIntLE 8 message.clOrdId
    ++ (encodeUIntLE 8 message.origClOrdId
    ++ (encodeUIntLE 8 message.securityId
    ++ (encodeUIntLE 8 message.execId
    ++ (encodeUIntLE 8 message.priceMkToLimitPx
    ++ (encodeUIntLE 8 message.yield
    ++ (encodeUIntLE 8 message.underlyingDirtyPrice
    ++ (encodeUIntLE 8 message.activityTime
    ++ (Alpha.encode message.filler1
    ++ (Alpha.encode message.filler2
    ++ (encodeUIntLE 4 message.leavesQty
    ++ (encodeUIntLE 4 message.cumQty
    ++ (encodeUIntLE 4 message.cxlQty
    ++ (Alpha.encode message.filler4v2
    ++ (OrdStatus.encode message.ordStatus
    ++ (ExecType.encode message.execType
    ++ (encodeUIntLE 2 message.execRestatementReason
    ++ (encodeUInt 1 message.productComplex
    ++ (encodeUInt 1 message.rolloverFlag)))))))))))))))))))))

def decode (bytes : List UInt8) : Option (ModifyOrderNrResponse × List UInt8) := do
  let (filler4, bytes) ← Alpha.decode 2 bytes
  let (nrResponseHeaderMeComp, bytes) ← NrResponseHeaderMeComp.decode bytes
  let (orderId, bytes) ← decodeUIntLE 8 bytes
  let (clOrdId, bytes) ← decodeUIntLE 8 bytes
  let (origClOrdId, bytes) ← decodeUIntLE 8 bytes
  let (securityId, bytes) ← decodeUIntLE 8 bytes
  let (execId, bytes) ← decodeUIntLE 8 bytes
  let (priceMkToLimitPx, bytes) ← decodeUIntLE 8 bytes
  let (yield, bytes) ← decodeUIntLE 8 bytes
  let (underlyingDirtyPrice, bytes) ← decodeUIntLE 8 bytes
  let (activityTime, bytes) ← decodeUIntLE 8 bytes
  let (filler1, bytes) ← Alpha.decode 8 bytes
  let (filler2, bytes) ← Alpha.decode 4 bytes
  let (leavesQty, bytes) ← decodeUIntLE 4 bytes
  let (cumQty, bytes) ← decodeUIntLE 4 bytes
  let (cxlQty, bytes) ← decodeUIntLE 4 bytes
  let (filler4v2, bytes) ← Alpha.decode 2 bytes
  let (ordStatus, bytes) ← OrdStatus.decode bytes
  let (execType, bytes) ← ExecType.decode bytes
  let (execRestatementReason, bytes) ← decodeUIntLE 2 bytes
  let (productComplex, bytes) ← decodeUInt 1 bytes
  let (rolloverFlag, bytes) ← decodeUInt 1 bytes
  pure ({ filler4, nrResponseHeaderMeComp, orderId, clOrdId, origClOrdId, securityId, execId, priceMkToLimitPx, yield, underlyingDirtyPrice, activityTime, filler1, filler2, leavesQty, cumQty, cxlQty, filler4v2, ordStatus, execType, execRestatementReason, productComplex, rolloverFlag }, bytes)

@[simp] theorem encode_length (message : ModifyOrderNrResponse) : (encode message).length = 162 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, NrResponseHeaderMeComp.encode_length, encodeUIntLE_length, OrdStatus.encode_length, ExecType.encode_length, encodeUInt_length]

theorem encode_length_pos (message : ModifyOrderNrResponse) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : ModifyOrderNrResponse) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, NrResponseHeaderMeComp.decode_encode, some_bind]
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
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, OrdStatus.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, ExecType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : ModifyOrderNrResponse) : decode (encode message) = some (message, []) :=
  List.append_nil (encode message) ▸ decode_encode message []

end ModifyOrderNrResponse

/-- Modify Order Response: 186 bytes -/
structure ModifyOrderResponse where
  filler4 : Alpha 2
  responseHeaderMeComp : ResponseHeaderMeComp
  orderId : BitVec 64
  clOrdId : BitVec 64
  origClOrdId : BitVec 64
  securityId : BitVec 64
  execId : BitVec 64
  priceMkToLimitPx : BitVec 64
  yield : BitVec 64
  underlyingDirtyPrice : BitVec 64
  trdRegTsTimePriority : BitVec 64
  activityTime : BitVec 64
  filler1 : Alpha 8
  filler2 : Alpha 4
  leavesQty : BitVec 32
  cumQty : BitVec 32
  cxlQty : BitVec 32
  filler4v2 : Alpha 2
  ordStatus : OrdStatus
  execType : ExecType
  execRestatementReason : BitVec 16
  productComplex : BitVec 8
  rolloverFlag : BitVec 8
  deriving DecidableEq, Repr

namespace ModifyOrderResponse

def encode (message : ModifyOrderResponse) : List UInt8 :=
  Alpha.encode message.filler4
    ++ (ResponseHeaderMeComp.encode message.responseHeaderMeComp
    ++ (encodeUIntLE 8 message.orderId
    ++ (encodeUIntLE 8 message.clOrdId
    ++ (encodeUIntLE 8 message.origClOrdId
    ++ (encodeUIntLE 8 message.securityId
    ++ (encodeUIntLE 8 message.execId
    ++ (encodeUIntLE 8 message.priceMkToLimitPx
    ++ (encodeUIntLE 8 message.yield
    ++ (encodeUIntLE 8 message.underlyingDirtyPrice
    ++ (encodeUIntLE 8 message.trdRegTsTimePriority
    ++ (encodeUIntLE 8 message.activityTime
    ++ (Alpha.encode message.filler1
    ++ (Alpha.encode message.filler2
    ++ (encodeUIntLE 4 message.leavesQty
    ++ (encodeUIntLE 4 message.cumQty
    ++ (encodeUIntLE 4 message.cxlQty
    ++ (Alpha.encode message.filler4v2
    ++ (OrdStatus.encode message.ordStatus
    ++ (ExecType.encode message.execType
    ++ (encodeUIntLE 2 message.execRestatementReason
    ++ (encodeUInt 1 message.productComplex
    ++ (encodeUInt 1 message.rolloverFlag))))))))))))))))))))))

def decode (bytes : List UInt8) : Option (ModifyOrderResponse × List UInt8) := do
  let (filler4, bytes) ← Alpha.decode 2 bytes
  let (responseHeaderMeComp, bytes) ← ResponseHeaderMeComp.decode bytes
  let (orderId, bytes) ← decodeUIntLE 8 bytes
  let (clOrdId, bytes) ← decodeUIntLE 8 bytes
  let (origClOrdId, bytes) ← decodeUIntLE 8 bytes
  let (securityId, bytes) ← decodeUIntLE 8 bytes
  let (execId, bytes) ← decodeUIntLE 8 bytes
  let (priceMkToLimitPx, bytes) ← decodeUIntLE 8 bytes
  let (yield, bytes) ← decodeUIntLE 8 bytes
  let (underlyingDirtyPrice, bytes) ← decodeUIntLE 8 bytes
  let (trdRegTsTimePriority, bytes) ← decodeUIntLE 8 bytes
  let (activityTime, bytes) ← decodeUIntLE 8 bytes
  let (filler1, bytes) ← Alpha.decode 8 bytes
  let (filler2, bytes) ← Alpha.decode 4 bytes
  let (leavesQty, bytes) ← decodeUIntLE 4 bytes
  let (cumQty, bytes) ← decodeUIntLE 4 bytes
  let (cxlQty, bytes) ← decodeUIntLE 4 bytes
  let (filler4v2, bytes) ← Alpha.decode 2 bytes
  let (ordStatus, bytes) ← OrdStatus.decode bytes
  let (execType, bytes) ← ExecType.decode bytes
  let (execRestatementReason, bytes) ← decodeUIntLE 2 bytes
  let (productComplex, bytes) ← decodeUInt 1 bytes
  let (rolloverFlag, bytes) ← decodeUInt 1 bytes
  pure ({ filler4, responseHeaderMeComp, orderId, clOrdId, origClOrdId, securityId, execId, priceMkToLimitPx, yield, underlyingDirtyPrice, trdRegTsTimePriority, activityTime, filler1, filler2, leavesQty, cumQty, cxlQty, filler4v2, ordStatus, execType, execRestatementReason, productComplex, rolloverFlag }, bytes)

@[simp] theorem encode_length (message : ModifyOrderResponse) : (encode message).length = 186 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, ResponseHeaderMeComp.encode_length, encodeUIntLE_length, OrdStatus.encode_length, ExecType.encode_length, encodeUInt_length]

theorem encode_length_pos (message : ModifyOrderResponse) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : ModifyOrderResponse) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, ResponseHeaderMeComp.decode_encode, some_bind]
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
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, OrdStatus.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, ExecType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : ModifyOrderResponse) : decode (encode message) = some (message, []) :=
  List.append_nil (encode message) ▸ decode_encode message []

end ModifyOrderResponse

/-- Multi Leg Grp Comp: 56 bytes -/
structure MultiLegGrpComp where
  securityId : BitVec 64
  orderId : BitVec 64
  price : BitVec 64
  maxPricePercentage : BitVec 64
  messageTag : BitVec 32
  orderQty : BitVec 32
  cumQty : BitVec 32
  cxlQty : BitVec 32
  execRestatementReason : BitVec 16
  ordStatus : OrdStatus
  execType : ExecType
  side : BitVec 8
  ordType : BitVec 8
  pad2 : Alpha 2
  deriving DecidableEq, Repr

namespace MultiLegGrpComp

def encode (message : MultiLegGrpComp) : List UInt8 :=
  encodeUIntLE 8 message.securityId
    ++ (encodeUIntLE 8 message.orderId
    ++ (encodeUIntLE 8 message.price
    ++ (encodeUIntLE 8 message.maxPricePercentage
    ++ (encodeUIntLE 4 message.messageTag
    ++ (encodeUIntLE 4 message.orderQty
    ++ (encodeUIntLE 4 message.cumQty
    ++ (encodeUIntLE 4 message.cxlQty
    ++ (encodeUIntLE 2 message.execRestatementReason
    ++ (OrdStatus.encode message.ordStatus
    ++ (ExecType.encode message.execType
    ++ (encodeUInt 1 message.side
    ++ (encodeUInt 1 message.ordType
    ++ (Alpha.encode message.pad2)))))))))))))

def decode (bytes : List UInt8) : Option (MultiLegGrpComp × List UInt8) := do
  let (securityId, bytes) ← decodeUIntLE 8 bytes
  let (orderId, bytes) ← decodeUIntLE 8 bytes
  let (price, bytes) ← decodeUIntLE 8 bytes
  let (maxPricePercentage, bytes) ← decodeUIntLE 8 bytes
  let (messageTag, bytes) ← decodeUIntLE 4 bytes
  let (orderQty, bytes) ← decodeUIntLE 4 bytes
  let (cumQty, bytes) ← decodeUIntLE 4 bytes
  let (cxlQty, bytes) ← decodeUIntLE 4 bytes
  let (execRestatementReason, bytes) ← decodeUIntLE 2 bytes
  let (ordStatus, bytes) ← OrdStatus.decode bytes
  let (execType, bytes) ← ExecType.decode bytes
  let (side, bytes) ← decodeUInt 1 bytes
  let (ordType, bytes) ← decodeUInt 1 bytes
  let (pad2, bytes) ← Alpha.decode 2 bytes
  pure ({ securityId, orderId, price, maxPricePercentage, messageTag, orderQty, cumQty, cxlQty, execRestatementReason, ordStatus, execType, side, ordType, pad2 }, bytes)

@[simp] theorem encode_length (message : MultiLegGrpComp) : (encode message).length = 56 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, OrdStatus.encode_length, ExecType.encode_length, encodeUInt_length, Alpha.encode_length]

theorem encode_length_pos (message : MultiLegGrpComp) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : MultiLegGrpComp) (rest : List UInt8) :
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
  rw [List.append_assoc, OrdStatus.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, ExecType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end MultiLegGrpComp

/-- Multi Leg Fill Grp Comp: 32 bytes -/
structure MultiLegFillGrpComp where
  fillPx : BitVec 64
  securityId : BitVec 64
  fillQty : BitVec 32
  fillMatchId : BitVec 32
  fillExecId : BitVec 32
  pad4 : Alpha 4
  deriving DecidableEq, Repr

namespace MultiLegFillGrpComp

def encode (message : MultiLegFillGrpComp) : List UInt8 :=
  encodeUIntLE 8 message.fillPx
    ++ (encodeUIntLE 8 message.securityId
    ++ (encodeUIntLE 4 message.fillQty
    ++ (encodeUIntLE 4 message.fillMatchId
    ++ (encodeUIntLE 4 message.fillExecId
    ++ (Alpha.encode message.pad4)))))

def decode (bytes : List UInt8) : Option (MultiLegFillGrpComp × List UInt8) := do
  let (fillPx, bytes) ← decodeUIntLE 8 bytes
  let (securityId, bytes) ← decodeUIntLE 8 bytes
  let (fillQty, bytes) ← decodeUIntLE 4 bytes
  let (fillMatchId, bytes) ← decodeUIntLE 4 bytes
  let (fillExecId, bytes) ← decodeUIntLE 4 bytes
  let (pad4, bytes) ← Alpha.decode 4 bytes
  pure ({ fillPx, securityId, fillQty, fillMatchId, fillExecId, pad4 }, bytes)

@[simp] theorem encode_length (message : MultiLegFillGrpComp) : (encode message).length = 32 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length]

theorem encode_length_pos (message : MultiLegFillGrpComp) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : MultiLegFillGrpComp) (rest : List UInt8) :
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
  rw [Alpha.decode_encode, some_bind]
  rfl

end MultiLegFillGrpComp

/-- Instrmnt Leg Exec Grp Comp: 32 bytes -/
structure InstrmntLegExecGrpComp where
  legSecurityId : BitVec 64
  legLastPx : BitVec 64
  legLastQty : BitVec 32
  legExecId : BitVec 32
  legSide : BitVec 8
  noFillsIndex : BitVec 8
  pad6 : Alpha 6
  deriving DecidableEq, Repr

namespace InstrmntLegExecGrpComp

def encode (message : InstrmntLegExecGrpComp) : List UInt8 :=
  encodeUIntLE 8 message.legSecurityId
    ++ (encodeUIntLE 8 message.legLastPx
    ++ (encodeUIntLE 4 message.legLastQty
    ++ (encodeUIntLE 4 message.legExecId
    ++ (encodeUInt 1 message.legSide
    ++ (encodeUInt 1 message.noFillsIndex
    ++ (Alpha.encode message.pad6))))))

def decode (bytes : List UInt8) : Option (InstrmntLegExecGrpComp × List UInt8) := do
  let (legSecurityId, bytes) ← decodeUIntLE 8 bytes
  let (legLastPx, bytes) ← decodeUIntLE 8 bytes
  let (legLastQty, bytes) ← decodeUIntLE 4 bytes
  let (legExecId, bytes) ← decodeUIntLE 4 bytes
  let (legSide, bytes) ← decodeUInt 1 bytes
  let (noFillsIndex, bytes) ← decodeUInt 1 bytes
  let (pad6, bytes) ← Alpha.decode 6 bytes
  pure ({ legSecurityId, legLastPx, legLastQty, legExecId, legSide, noFillsIndex, pad6 }, bytes)

@[simp] theorem encode_length (message : InstrmntLegExecGrpComp) : (encode message).length = 32 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, encodeUInt_length, Alpha.encode_length]

theorem encode_length_pos (message : InstrmntLegExecGrpComp) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : InstrmntLegExecGrpComp) (rest : List UInt8) :
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
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end InstrmntLegExecGrpComp

/-- Multi Leg Exec Report Broadcast -/
structure MultiLegExecReportBroadcast where
  filler4 : Alpha 2
  rbcHeaderMeComp : RbcHeaderMeComp
  senderLocationId : BitVec 64
  clOrdId : BitVec 64
  execId : BitVec 64
  accountType : BitVec 8
  algoId : Alpha 16
  clientCode : Alpha 12
  cpCode : Alpha 12
  pad3 : Alpha 3
  multiLegGrpComp : Bounded 1 MultiLegGrpComp
  multiLegFillGrpComp : Bounded 1 MultiLegFillGrpComp
  instrmntLegExecGrpComp : Bounded 2 InstrmntLegExecGrpComp
  deriving DecidableEq, Repr

namespace MultiLegExecReportBroadcast

def encode (message : MultiLegExecReportBroadcast) : List UInt8 :=
  Alpha.encode message.filler4
    ++ (RbcHeaderMeComp.encode message.rbcHeaderMeComp
    ++ (encodeUIntLE 8 message.senderLocationId
    ++ (encodeUIntLE 8 message.clOrdId
    ++ (encodeUIntLE 8 message.execId
    ++ (encodeUIntLE 2 (BitVec.ofNat (8 * 2) message.instrmntLegExecGrpComp.val.length)
    ++ (encodeUInt 1 message.accountType
    ++ (encodeUInt 1 (BitVec.ofNat (8 * 1) message.multiLegGrpComp.val.length)
    ++ (encodeUInt 1 (BitVec.ofNat (8 * 1) message.multiLegFillGrpComp.val.length)
    ++ (Alpha.encode message.algoId
    ++ (Alpha.encode message.clientCode
    ++ (Alpha.encode message.cpCode
    ++ (Alpha.encode message.pad3
    ++ (encodeMany MultiLegGrpComp.encode message.multiLegGrpComp.val
    ++ (encodeMany MultiLegFillGrpComp.encode message.multiLegFillGrpComp.val
    ++ (encodeMany InstrmntLegExecGrpComp.encode message.instrmntLegExecGrpComp.val)))))))))))))))

def decode (bytes : List UInt8) : Option (MultiLegExecReportBroadcast × List UInt8) := do
  let (filler4, bytes) ← Alpha.decode 2 bytes
  let (rbcHeaderMeComp, bytes) ← RbcHeaderMeComp.decode bytes
  let (senderLocationId, bytes) ← decodeUIntLE 8 bytes
  let (clOrdId, bytes) ← decodeUIntLE 8 bytes
  let (execId, bytes) ← decodeUIntLE 8 bytes
  let (noLegExecs, bytes) ← decodeUIntLE 2 bytes
  let (accountType, bytes) ← decodeUInt 1 bytes
  let (noOfMultiLeg, bytes) ← decodeUInt 1 bytes
  let (noOfMultiLegExecs, bytes) ← decodeUInt 1 bytes
  let (algoId, bytes) ← Alpha.decode 16 bytes
  let (clientCode, bytes) ← Alpha.decode 12 bytes
  let (cpCode, bytes) ← Alpha.decode 12 bytes
  let (pad3, bytes) ← Alpha.decode 3 bytes
  let (multiLegGrpComp_, bytes) ← decodeMany MultiLegGrpComp.decode noOfMultiLeg.toNat bytes
  let (multiLegFillGrpComp_, bytes) ← decodeMany MultiLegFillGrpComp.decode noOfMultiLegExecs.toNat bytes
  let (instrmntLegExecGrpComp_, bytes) ← decodeMany InstrmntLegExecGrpComp.decode noLegExecs.toNat bytes
  if fits_multiLegGrpComp : multiLegGrpComp_.length < 256 ^ 1 then
    if fits_multiLegFillGrpComp : multiLegFillGrpComp_.length < 256 ^ 1 then
      if fits_instrmntLegExecGrpComp : instrmntLegExecGrpComp_.length < 256 ^ 2 then
        pure ({ filler4, rbcHeaderMeComp, senderLocationId, clOrdId, execId, accountType, algoId, clientCode, cpCode, pad3, multiLegGrpComp := ⟨multiLegGrpComp_, fits_multiLegGrpComp⟩, multiLegFillGrpComp := ⟨multiLegFillGrpComp_, fits_multiLegFillGrpComp⟩, instrmntLegExecGrpComp := ⟨instrmntLegExecGrpComp_, fits_instrmntLegExecGrpComp⟩ }, bytes)
      else none
    else none
  else none

theorem encode_length_pos (message : MultiLegExecReportBroadcast) : (encode message).length > 0 := by
  unfold encode
  simp only [Alpha.encode_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : MultiLegExecReportBroadcast) : (encode message).length ≤ 2119682 := by
  have bound_multiLegGrpComp := message.multiLegGrpComp.length_lt
  have bound_multiLegFillGrpComp := message.multiLegFillGrpComp.length_lt
  have bound_instrmntLegExecGrpComp := message.instrmntLegExecGrpComp.length_lt
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, Alpha.encode_length, RbcHeaderMeComp.encode_length, encodeUIntLE_length, encodeUInt_length, encodeMany_length_const MultiLegGrpComp.encode 56 MultiLegGrpComp.encode_length, encodeMany_length_const MultiLegFillGrpComp.encode 32 MultiLegFillGrpComp.encode_length, encodeMany_length_const InstrmntLegExecGrpComp.encode 32 InstrmntLegExecGrpComp.encode_length]
  omega

@[simp] theorem decode_encode (message : MultiLegExecReportBroadcast) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, RbcHeaderMeComp.decode_encode, some_bind]
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
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
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
  rw [List.append_assoc, decodeMany_bounded 1 MultiLegGrpComp.encode MultiLegGrpComp.decode MultiLegGrpComp.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeMany_bounded 1 MultiLegFillGrpComp.encode MultiLegFillGrpComp.decode MultiLegFillGrpComp.decode_encode, some_bind]
  dsimp only
  rw [decodeMany_bounded 2 InstrmntLegExecGrpComp.encode InstrmntLegExecGrpComp.decode InstrmntLegExecGrpComp.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.multiLegGrpComp.length_lt, dite_eq_left message.multiLegFillGrpComp.length_lt, dite_eq_left message.instrmntLegExecGrpComp.length_lt]
  rfl

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : MultiLegExecReportBroadcast) : decode (encode message) = some (message, []) :=
  List.append_nil (encode message) ▸ decode_encode message []

end MultiLegExecReportBroadcast

/-- Multi Leg Exec Grp Comp: 32 bytes -/
structure MultiLegExecGrpComp where
  orderId : BitVec 64
  securityId : BitVec 64
  cumQty : BitVec 32
  cxlQty : BitVec 32
  execRestatementReason : BitVec 16
  ordStatus : OrdStatus
  execType : ExecType
  pad4 : Alpha 4
  deriving DecidableEq, Repr

namespace MultiLegExecGrpComp

def encode (message : MultiLegExecGrpComp) : List UInt8 :=
  encodeUIntLE 8 message.orderId
    ++ (encodeUIntLE 8 message.securityId
    ++ (encodeUIntLE 4 message.cumQty
    ++ (encodeUIntLE 4 message.cxlQty
    ++ (encodeUIntLE 2 message.execRestatementReason
    ++ (OrdStatus.encode message.ordStatus
    ++ (ExecType.encode message.execType
    ++ (Alpha.encode message.pad4)))))))

def decode (bytes : List UInt8) : Option (MultiLegExecGrpComp × List UInt8) := do
  let (orderId, bytes) ← decodeUIntLE 8 bytes
  let (securityId, bytes) ← decodeUIntLE 8 bytes
  let (cumQty, bytes) ← decodeUIntLE 4 bytes
  let (cxlQty, bytes) ← decodeUIntLE 4 bytes
  let (execRestatementReason, bytes) ← decodeUIntLE 2 bytes
  let (ordStatus, bytes) ← OrdStatus.decode bytes
  let (execType, bytes) ← ExecType.decode bytes
  let (pad4, bytes) ← Alpha.decode 4 bytes
  pure ({ orderId, securityId, cumQty, cxlQty, execRestatementReason, ordStatus, execType, pad4 }, bytes)

@[simp] theorem encode_length (message : MultiLegExecGrpComp) : (encode message).length = 32 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, OrdStatus.encode_length, ExecType.encode_length, Alpha.encode_length]

theorem encode_length_pos (message : MultiLegExecGrpComp) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : MultiLegExecGrpComp) (rest : List UInt8) :
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
  rw [List.append_assoc, OrdStatus.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, ExecType.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end MultiLegExecGrpComp

/-- Multi Leg Exec Response -/
structure MultiLegExecResponse where
  filler4 : Alpha 2
  responseHeaderMeComp : ResponseHeaderMeComp
  clOrdId : BitVec 64
  execId : BitVec 64
  algoId : Alpha 16
  pad4 : Alpha 4
  multiLegExecGrpComp : Bounded 1 MultiLegExecGrpComp
  multiLegFillGrpComp : Bounded 1 MultiLegFillGrpComp
  instrmntLegExecGrpComp : Bounded 2 InstrmntLegExecGrpComp
  deriving DecidableEq, Repr

namespace MultiLegExecResponse

def encode (message : MultiLegExecResponse) : List UInt8 :=
  Alpha.encode message.filler4
    ++ (ResponseHeaderMeComp.encode message.responseHeaderMeComp
    ++ (encodeUIntLE 8 message.clOrdId
    ++ (encodeUIntLE 8 message.execId
    ++ (encodeUIntLE 2 (BitVec.ofNat (8 * 2) message.instrmntLegExecGrpComp.val.length)
    ++ (encodeUInt 1 (BitVec.ofNat (8 * 1) message.multiLegExecGrpComp.val.length)
    ++ (encodeUInt 1 (BitVec.ofNat (8 * 1) message.multiLegFillGrpComp.val.length)
    ++ (Alpha.encode message.algoId
    ++ (Alpha.encode message.pad4
    ++ (encodeMany MultiLegExecGrpComp.encode message.multiLegExecGrpComp.val
    ++ (encodeMany MultiLegFillGrpComp.encode message.multiLegFillGrpComp.val
    ++ (encodeMany InstrmntLegExecGrpComp.encode message.instrmntLegExecGrpComp.val)))))))))))

def decode (bytes : List UInt8) : Option (MultiLegExecResponse × List UInt8) := do
  let (filler4, bytes) ← Alpha.decode 2 bytes
  let (responseHeaderMeComp, bytes) ← ResponseHeaderMeComp.decode bytes
  let (clOrdId, bytes) ← decodeUIntLE 8 bytes
  let (execId, bytes) ← decodeUIntLE 8 bytes
  let (noLegExecs, bytes) ← decodeUIntLE 2 bytes
  let (noOfMultiLeg, bytes) ← decodeUInt 1 bytes
  let (noOfMultiLegExecs, bytes) ← decodeUInt 1 bytes
  let (algoId, bytes) ← Alpha.decode 16 bytes
  let (pad4, bytes) ← Alpha.decode 4 bytes
  let (multiLegExecGrpComp_, bytes) ← decodeMany MultiLegExecGrpComp.decode noOfMultiLeg.toNat bytes
  let (multiLegFillGrpComp_, bytes) ← decodeMany MultiLegFillGrpComp.decode noOfMultiLegExecs.toNat bytes
  let (instrmntLegExecGrpComp_, bytes) ← decodeMany InstrmntLegExecGrpComp.decode noLegExecs.toNat bytes
  if fits_multiLegExecGrpComp : multiLegExecGrpComp_.length < 256 ^ 1 then
    if fits_multiLegFillGrpComp : multiLegFillGrpComp_.length < 256 ^ 1 then
      if fits_instrmntLegExecGrpComp : instrmntLegExecGrpComp_.length < 256 ^ 2 then
        pure ({ filler4, responseHeaderMeComp, clOrdId, execId, algoId, pad4, multiLegExecGrpComp := ⟨multiLegExecGrpComp_, fits_multiLegExecGrpComp⟩, multiLegFillGrpComp := ⟨multiLegFillGrpComp_, fits_multiLegFillGrpComp⟩, instrmntLegExecGrpComp := ⟨instrmntLegExecGrpComp_, fits_instrmntLegExecGrpComp⟩ }, bytes)
      else none
    else none
  else none

theorem encode_length_pos (message : MultiLegExecResponse) : (encode message).length > 0 := by
  unfold encode
  simp only [Alpha.encode_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : MultiLegExecResponse) : (encode message).length ≤ 2113554 := by
  have bound_multiLegExecGrpComp := message.multiLegExecGrpComp.length_lt
  have bound_multiLegFillGrpComp := message.multiLegFillGrpComp.length_lt
  have bound_instrmntLegExecGrpComp := message.instrmntLegExecGrpComp.length_lt
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, Alpha.encode_length, ResponseHeaderMeComp.encode_length, encodeUIntLE_length, encodeUInt_length, encodeMany_length_const MultiLegExecGrpComp.encode 32 MultiLegExecGrpComp.encode_length, encodeMany_length_const MultiLegFillGrpComp.encode 32 MultiLegFillGrpComp.encode_length, encodeMany_length_const InstrmntLegExecGrpComp.encode 32 InstrmntLegExecGrpComp.encode_length]
  omega

@[simp] theorem decode_encode (message : MultiLegExecResponse) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, ResponseHeaderMeComp.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeMany_bounded 1 MultiLegExecGrpComp.encode MultiLegExecGrpComp.decode MultiLegExecGrpComp.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeMany_bounded 1 MultiLegFillGrpComp.encode MultiLegFillGrpComp.decode MultiLegFillGrpComp.decode_encode, some_bind]
  dsimp only
  rw [decodeMany_bounded 2 InstrmntLegExecGrpComp.encode InstrmntLegExecGrpComp.decode InstrmntLegExecGrpComp.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.multiLegExecGrpComp.length_lt, dite_eq_left message.multiLegFillGrpComp.length_lt, dite_eq_left message.instrmntLegExecGrpComp.length_lt]
  rfl

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : MultiLegExecResponse) : decode (encode message) = some (message, []) :=
  List.append_nil (encode message) ▸ decode_encode message []

end MultiLegExecResponse

/-- Multi Leg Order Reject -/
structure MultiLegOrderReject where
  filler4 : Alpha 2
  nrResponseHeaderMeComp : NrResponseHeaderMeComp
  securityId : BitVec 64
  sessionRejectReason : BitVec 32
  pad2 : Alpha 2
  varText : Bounded 2 UInt8
  alignmentPadding : Capped 7
  deriving DecidableEq, Repr

namespace MultiLegOrderReject

def encode (message : MultiLegOrderReject) : List UInt8 :=
  Alpha.encode message.filler4
    ++ (NrResponseHeaderMeComp.encode message.nrResponseHeaderMeComp
    ++ (encodeUIntLE 8 message.securityId
    ++ (encodeUIntLE 4 message.sessionRejectReason
    ++ (encodeUIntLE 2 (BitVec.ofNat (8 * 2) message.varText.val.length)
    ++ (Alpha.encode message.pad2
    ++ (encodeMany Byte.encode message.varText.val
    ++ (message.alignmentPadding.val)))))))

def decode (bytes : List UInt8) : Option MultiLegOrderReject := do
  let (filler4, bytes) ← Alpha.decode 2 bytes
  let (nrResponseHeaderMeComp, bytes) ← NrResponseHeaderMeComp.decode bytes
  let (securityId, bytes) ← decodeUIntLE 8 bytes
  let (sessionRejectReason, bytes) ← decodeUIntLE 4 bytes
  let (varTextLen, bytes) ← decodeUIntLE 2 bytes
  let (pad2, bytes) ← Alpha.decode 2 bytes
  let (varText_, bytes) ← decodeMany Byte.decode varTextLen.toNat bytes
  let alignmentPadding_ := bytes
  if fits_varText : varText_.length < 256 ^ 2 then
    if fits_alignmentPadding : alignmentPadding_.length ≤ 7 then
      pure { filler4, nrResponseHeaderMeComp, securityId, sessionRejectReason, pad2, varText := ⟨varText_, fits_varText⟩, alignmentPadding := ⟨alignmentPadding_, fits_alignmentPadding⟩ }
    else none
  else none

theorem encode_length_pos (message : MultiLegOrderReject) : (encode message).length > 0 := by
  unfold encode
  simp only [Alpha.encode_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : MultiLegOrderReject) : (encode message).length ≤ 65616 := by
  have bound_varText := message.varText.length_lt
  have bound_alignmentPadding := message.alignmentPadding.length_le
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, Alpha.encode_length, NrResponseHeaderMeComp.encode_length, encodeUIntLE_length, encodeMany_length_const Byte.encode 1 Byte.encode_length]
  omega

theorem decode_encode (message : MultiLegOrderReject) : decode (encode message) = some message := by
  unfold decode encode
  rw [Alpha.decode_encode, some_bind]
  dsimp only
  rw [NrResponseHeaderMeComp.decode_encode, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  dsimp only
  rw [decodeMany_bounded 2 Byte.encode Byte.decode Byte.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.varText.length_lt, dite_eq_left message.alignmentPadding.length_le]
  rfl

end MultiLegOrderReject

/-- New Order Nr Response: 146 bytes -/
structure NewOrderNrResponse where
  filler4 : Alpha 2
  nrResponseHeaderMeComp : NrResponseHeaderMeComp
  orderId : BitVec 64
  clOrdId : BitVec 64
  securityId : BitVec 64
  priceMkToLimitPx : BitVec 64
  yield : BitVec 64
  underlyingDirtyPrice : BitVec 64
  execId : BitVec 64
  activityTime : BitVec 64
  filler1 : Alpha 8
  filler2 : Alpha 4
  filler4v2 : Alpha 2
  ordStatus : OrdStatus
  execType : ExecType
  execRestatementReason : BitVec 16
  productComplex : BitVec 8
  rolloverFlag : BitVec 8
  pad4 : Alpha 4
  deriving DecidableEq, Repr

namespace NewOrderNrResponse

def encode (message : NewOrderNrResponse) : List UInt8 :=
  Alpha.encode message.filler4
    ++ (NrResponseHeaderMeComp.encode message.nrResponseHeaderMeComp
    ++ (encodeUIntLE 8 message.orderId
    ++ (encodeUIntLE 8 message.clOrdId
    ++ (encodeUIntLE 8 message.securityId
    ++ (encodeUIntLE 8 message.priceMkToLimitPx
    ++ (encodeUIntLE 8 message.yield
    ++ (encodeUIntLE 8 message.underlyingDirtyPrice
    ++ (encodeUIntLE 8 message.execId
    ++ (encodeUIntLE 8 message.activityTime
    ++ (Alpha.encode message.filler1
    ++ (Alpha.encode message.filler2
    ++ (Alpha.encode message.filler4v2
    ++ (OrdStatus.encode message.ordStatus
    ++ (ExecType.encode message.execType
    ++ (encodeUIntLE 2 message.execRestatementReason
    ++ (encodeUInt 1 message.productComplex
    ++ (encodeUInt 1 message.rolloverFlag
    ++ (Alpha.encode message.pad4))))))))))))))))))

def decode (bytes : List UInt8) : Option (NewOrderNrResponse × List UInt8) := do
  let (filler4, bytes) ← Alpha.decode 2 bytes
  let (nrResponseHeaderMeComp, bytes) ← NrResponseHeaderMeComp.decode bytes
  let (orderId, bytes) ← decodeUIntLE 8 bytes
  let (clOrdId, bytes) ← decodeUIntLE 8 bytes
  let (securityId, bytes) ← decodeUIntLE 8 bytes
  let (priceMkToLimitPx, bytes) ← decodeUIntLE 8 bytes
  let (yield, bytes) ← decodeUIntLE 8 bytes
  let (underlyingDirtyPrice, bytes) ← decodeUIntLE 8 bytes
  let (execId, bytes) ← decodeUIntLE 8 bytes
  let (activityTime, bytes) ← decodeUIntLE 8 bytes
  let (filler1, bytes) ← Alpha.decode 8 bytes
  let (filler2, bytes) ← Alpha.decode 4 bytes
  let (filler4v2, bytes) ← Alpha.decode 2 bytes
  let (ordStatus, bytes) ← OrdStatus.decode bytes
  let (execType, bytes) ← ExecType.decode bytes
  let (execRestatementReason, bytes) ← decodeUIntLE 2 bytes
  let (productComplex, bytes) ← decodeUInt 1 bytes
  let (rolloverFlag, bytes) ← decodeUInt 1 bytes
  let (pad4, bytes) ← Alpha.decode 4 bytes
  pure ({ filler4, nrResponseHeaderMeComp, orderId, clOrdId, securityId, priceMkToLimitPx, yield, underlyingDirtyPrice, execId, activityTime, filler1, filler2, filler4v2, ordStatus, execType, execRestatementReason, productComplex, rolloverFlag, pad4 }, bytes)

@[simp] theorem encode_length (message : NewOrderNrResponse) : (encode message).length = 146 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, NrResponseHeaderMeComp.encode_length, encodeUIntLE_length, OrdStatus.encode_length, ExecType.encode_length, encodeUInt_length]

theorem encode_length_pos (message : NewOrderNrResponse) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : NewOrderNrResponse) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, NrResponseHeaderMeComp.decode_encode, some_bind]
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
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, OrdStatus.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, ExecType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : NewOrderNrResponse) : decode (encode message) = some (message, []) :=
  List.append_nil (encode message) ▸ decode_encode message []

end NewOrderNrResponse

/-- New Order Response: 178 bytes -/
structure NewOrderResponse where
  filler4 : Alpha 2
  responseHeaderMeComp : ResponseHeaderMeComp
  orderId : BitVec 64
  clOrdId : BitVec 64
  securityId : BitVec 64
  priceMkToLimitPx : BitVec 64
  yield : BitVec 64
  underlyingDirtyPrice : BitVec 64
  execId : BitVec 64
  trdRegTsEntryTime : BitVec 64
  trdRegTsTimePriority : BitVec 64
  activityTime : BitVec 64
  filler1 : Alpha 8
  filler2 : Alpha 4
  filler4v2 : Alpha 2
  ordStatus : OrdStatus
  execType : ExecType
  execRestatementReason : BitVec 16
  productComplex : BitVec 8
  rolloverFlag : BitVec 8
  pad4 : Alpha 4
  deriving DecidableEq, Repr

namespace NewOrderResponse

def encode (message : NewOrderResponse) : List UInt8 :=
  Alpha.encode message.filler4
    ++ (ResponseHeaderMeComp.encode message.responseHeaderMeComp
    ++ (encodeUIntLE 8 message.orderId
    ++ (encodeUIntLE 8 message.clOrdId
    ++ (encodeUIntLE 8 message.securityId
    ++ (encodeUIntLE 8 message.priceMkToLimitPx
    ++ (encodeUIntLE 8 message.yield
    ++ (encodeUIntLE 8 message.underlyingDirtyPrice
    ++ (encodeUIntLE 8 message.execId
    ++ (encodeUIntLE 8 message.trdRegTsEntryTime
    ++ (encodeUIntLE 8 message.trdRegTsTimePriority
    ++ (encodeUIntLE 8 message.activityTime
    ++ (Alpha.encode message.filler1
    ++ (Alpha.encode message.filler2
    ++ (Alpha.encode message.filler4v2
    ++ (OrdStatus.encode message.ordStatus
    ++ (ExecType.encode message.execType
    ++ (encodeUIntLE 2 message.execRestatementReason
    ++ (encodeUInt 1 message.productComplex
    ++ (encodeUInt 1 message.rolloverFlag
    ++ (Alpha.encode message.pad4))))))))))))))))))))

def decode (bytes : List UInt8) : Option (NewOrderResponse × List UInt8) := do
  let (filler4, bytes) ← Alpha.decode 2 bytes
  let (responseHeaderMeComp, bytes) ← ResponseHeaderMeComp.decode bytes
  let (orderId, bytes) ← decodeUIntLE 8 bytes
  let (clOrdId, bytes) ← decodeUIntLE 8 bytes
  let (securityId, bytes) ← decodeUIntLE 8 bytes
  let (priceMkToLimitPx, bytes) ← decodeUIntLE 8 bytes
  let (yield, bytes) ← decodeUIntLE 8 bytes
  let (underlyingDirtyPrice, bytes) ← decodeUIntLE 8 bytes
  let (execId, bytes) ← decodeUIntLE 8 bytes
  let (trdRegTsEntryTime, bytes) ← decodeUIntLE 8 bytes
  let (trdRegTsTimePriority, bytes) ← decodeUIntLE 8 bytes
  let (activityTime, bytes) ← decodeUIntLE 8 bytes
  let (filler1, bytes) ← Alpha.decode 8 bytes
  let (filler2, bytes) ← Alpha.decode 4 bytes
  let (filler4v2, bytes) ← Alpha.decode 2 bytes
  let (ordStatus, bytes) ← OrdStatus.decode bytes
  let (execType, bytes) ← ExecType.decode bytes
  let (execRestatementReason, bytes) ← decodeUIntLE 2 bytes
  let (productComplex, bytes) ← decodeUInt 1 bytes
  let (rolloverFlag, bytes) ← decodeUInt 1 bytes
  let (pad4, bytes) ← Alpha.decode 4 bytes
  pure ({ filler4, responseHeaderMeComp, orderId, clOrdId, securityId, priceMkToLimitPx, yield, underlyingDirtyPrice, execId, trdRegTsEntryTime, trdRegTsTimePriority, activityTime, filler1, filler2, filler4v2, ordStatus, execType, execRestatementReason, productComplex, rolloverFlag, pad4 }, bytes)

@[simp] theorem encode_length (message : NewOrderResponse) : (encode message).length = 178 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, ResponseHeaderMeComp.encode_length, encodeUIntLE_length, OrdStatus.encode_length, ExecType.encode_length, encodeUInt_length]

theorem encode_length_pos (message : NewOrderResponse) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : NewOrderResponse) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, ResponseHeaderMeComp.decode_encode, some_bind]
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
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, OrdStatus.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, ExecType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : NewOrderResponse) : decode (encode message) = some (message, []) :=
  List.append_nil (encode message) ▸ decode_encode message []

end NewOrderResponse

/-- Rbc Header Comp: 32 bytes -/
structure RbcHeaderComp where
  sendingTime : BitVec 64
  applSeqNum : BitVec 64
  applSubId : BitVec 32
  partitionId : BitVec 16
  applResendFlag : BitVec 8
  applId : BitVec 8
  lastFragment : BitVec 8
  pad7 : Alpha 7
  deriving DecidableEq, Repr

namespace RbcHeaderComp

def encode (message : RbcHeaderComp) : List UInt8 :=
  encodeUIntLE 8 message.sendingTime
    ++ (encodeUIntLE 8 message.applSeqNum
    ++ (encodeUIntLE 4 message.applSubId
    ++ (encodeUIntLE 2 message.partitionId
    ++ (encodeUInt 1 message.applResendFlag
    ++ (encodeUInt 1 message.applId
    ++ (encodeUInt 1 message.lastFragment
    ++ (Alpha.encode message.pad7)))))))

def decode (bytes : List UInt8) : Option (RbcHeaderComp × List UInt8) := do
  let (sendingTime, bytes) ← decodeUIntLE 8 bytes
  let (applSeqNum, bytes) ← decodeUIntLE 8 bytes
  let (applSubId, bytes) ← decodeUIntLE 4 bytes
  let (partitionId, bytes) ← decodeUIntLE 2 bytes
  let (applResendFlag, bytes) ← decodeUInt 1 bytes
  let (applId, bytes) ← decodeUInt 1 bytes
  let (lastFragment, bytes) ← decodeUInt 1 bytes
  let (pad7, bytes) ← Alpha.decode 7 bytes
  pure ({ sendingTime, applSeqNum, applSubId, partitionId, applResendFlag, applId, lastFragment, pad7 }, bytes)

@[simp] theorem encode_length (message : RbcHeaderComp) : (encode message).length = 32 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, encodeUInt_length, Alpha.encode_length]

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
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end RbcHeaderComp

/-- News Broadcast -/
structure NewsBroadcast where
  filler4 : Alpha 2
  rbcHeaderComp : RbcHeaderComp
  origTime : BitVec 64
  headline : Alpha 256
  pad6 : Alpha 6
  varText : Bounded 2 UInt8
  alignmentPadding : Capped 7
  deriving DecidableEq, Repr

namespace NewsBroadcast

def encode (message : NewsBroadcast) : List UInt8 :=
  Alpha.encode message.filler4
    ++ (RbcHeaderComp.encode message.rbcHeaderComp
    ++ (encodeUIntLE 8 message.origTime
    ++ (encodeUIntLE 2 (BitVec.ofNat (8 * 2) message.varText.val.length)
    ++ (Alpha.encode message.headline
    ++ (Alpha.encode message.pad6
    ++ (encodeMany Byte.encode message.varText.val
    ++ (message.alignmentPadding.val)))))))

def decode (bytes : List UInt8) : Option NewsBroadcast := do
  let (filler4, bytes) ← Alpha.decode 2 bytes
  let (rbcHeaderComp, bytes) ← RbcHeaderComp.decode bytes
  let (origTime, bytes) ← decodeUIntLE 8 bytes
  let (varTextLen, bytes) ← decodeUIntLE 2 bytes
  let (headline, bytes) ← Alpha.decode 256 bytes
  let (pad6, bytes) ← Alpha.decode 6 bytes
  let (varText_, bytes) ← decodeMany Byte.decode varTextLen.toNat bytes
  let alignmentPadding_ := bytes
  if fits_varText : varText_.length < 256 ^ 2 then
    if fits_alignmentPadding : alignmentPadding_.length ≤ 7 then
      pure { filler4, rbcHeaderComp, origTime, headline, pad6, varText := ⟨varText_, fits_varText⟩, alignmentPadding := ⟨alignmentPadding_, fits_alignmentPadding⟩ }
    else none
  else none

theorem encode_length_pos (message : NewsBroadcast) : (encode message).length > 0 := by
  unfold encode
  simp only [Alpha.encode_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : NewsBroadcast) : (encode message).length ≤ 65848 := by
  have bound_varText := message.varText.length_lt
  have bound_alignmentPadding := message.alignmentPadding.length_le
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, Alpha.encode_length, RbcHeaderComp.encode_length, encodeUIntLE_length, encodeMany_length_const Byte.encode 1 Byte.encode_length]
  omega

theorem decode_encode (message : NewsBroadcast) : decode (encode message) = some message := by
  unfold decode encode
  rw [Alpha.decode_encode, some_bind]
  dsimp only
  rw [RbcHeaderComp.decode_encode, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  dsimp only
  rw [decodeMany_bounded 2 Byte.encode Byte.decode Byte.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.varText.length_lt, dite_eq_left message.alignmentPadding.length_le]
  rfl

end NewsBroadcast

/-- Fills Grp Comp: 40 bytes -/
structure FillsGrpComp where
  fillPx : BitVec 64
  fillYield : BitVec 64
  fillDirtyPx : BitVec 64
  fillQty : BitVec 32
  fillMatchId : BitVec 32
  fillExecId : BitVec 32
  fillLiquidityInd : BitVec 8
  pad3 : Alpha 3
  deriving DecidableEq, Repr

namespace FillsGrpComp

def encode (message : FillsGrpComp) : List UInt8 :=
  encodeUIntLE 8 message.fillPx
    ++ (encodeUIntLE 8 message.fillYield
    ++ (encodeUIntLE 8 message.fillDirtyPx
    ++ (encodeUIntLE 4 message.fillQty
    ++ (encodeUIntLE 4 message.fillMatchId
    ++ (encodeUIntLE 4 message.fillExecId
    ++ (encodeUInt 1 message.fillLiquidityInd
    ++ (Alpha.encode message.pad3)))))))

def decode (bytes : List UInt8) : Option (FillsGrpComp × List UInt8) := do
  let (fillPx, bytes) ← decodeUIntLE 8 bytes
  let (fillYield, bytes) ← decodeUIntLE 8 bytes
  let (fillDirtyPx, bytes) ← decodeUIntLE 8 bytes
  let (fillQty, bytes) ← decodeUIntLE 4 bytes
  let (fillMatchId, bytes) ← decodeUIntLE 4 bytes
  let (fillExecId, bytes) ← decodeUIntLE 4 bytes
  let (fillLiquidityInd, bytes) ← decodeUInt 1 bytes
  let (pad3, bytes) ← Alpha.decode 3 bytes
  pure ({ fillPx, fillYield, fillDirtyPx, fillQty, fillMatchId, fillExecId, fillLiquidityInd, pad3 }, bytes)

@[simp] theorem encode_length (message : FillsGrpComp) : (encode message).length = 40 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, encodeUInt_length, Alpha.encode_length]

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

end FillsGrpComp

/-- Order Exec Notification -/
structure OrderExecNotification where
  filler4 : Alpha 2
  rbcHeaderMeComp : RbcHeaderMeComp
  orderId : BitVec 64
  senderLocationId : BitVec 64
  clOrdId : BitVec 64
  origClOrdId : BitVec 64
  securityId : BitVec 64
  execId : BitVec 64
  activityTime : BitVec 64
  filler1 : Alpha 8
  filler2 : Alpha 4
  messageTag : BitVec 32
  marketSegmentId : BitVec 32
  leavesQty : BitVec 32
  cumQty : BitVec 32
  cxlQty : BitVec 32
  filler4v2 : Alpha 2
  execRestatementReason : BitVec 16
  accountType : BitVec 8
  productComplex : BitVec 8
  ordStatus : OrdStatus
  execType : ExecType
  triggered : BitVec 8
  side : BitVec 8
  rolloverFlag : BitVec 8
  account : Alpha 2
  algoId : Alpha 16
  clientCode : Alpha 12
  cpCode : Alpha 12
  freeText3 : Alpha 12
  pad4 : Alpha 4
  fillsGrpComp : Bounded 1 FillsGrpComp
  instrmntLegExecGrpComp : Bounded 2 InstrmntLegExecGrpComp
  deriving DecidableEq, Repr

namespace OrderExecNotification

def encode (message : OrderExecNotification) : List UInt8 :=
  Alpha.encode message.filler4
    ++ (RbcHeaderMeComp.encode message.rbcHeaderMeComp
    ++ (encodeUIntLE 8 message.orderId
    ++ (encodeUIntLE 8 message.senderLocationId
    ++ (encodeUIntLE 8 message.clOrdId
    ++ (encodeUIntLE 8 message.origClOrdId
    ++ (encodeUIntLE 8 message.securityId
    ++ (encodeUIntLE 8 message.execId
    ++ (encodeUIntLE 8 message.activityTime
    ++ (Alpha.encode message.filler1
    ++ (Alpha.encode message.filler2
    ++ (encodeUIntLE 4 message.messageTag
    ++ (encodeUIntLE 4 message.marketSegmentId
    ++ (encodeUIntLE 4 message.leavesQty
    ++ (encodeUIntLE 4 message.cumQty
    ++ (encodeUIntLE 4 message.cxlQty
    ++ (encodeUIntLE 2 (BitVec.ofNat (8 * 2) message.instrmntLegExecGrpComp.val.length)
    ++ (Alpha.encode message.filler4v2
    ++ (encodeUIntLE 2 message.execRestatementReason
    ++ (encodeUInt 1 message.accountType
    ++ (encodeUInt 1 message.productComplex
    ++ (OrdStatus.encode message.ordStatus
    ++ (ExecType.encode message.execType
    ++ (encodeUInt 1 message.triggered
    ++ (encodeUInt 1 (BitVec.ofNat (8 * 1) message.fillsGrpComp.val.length)
    ++ (encodeUInt 1 message.side
    ++ (encodeUInt 1 message.rolloverFlag
    ++ (Alpha.encode message.account
    ++ (Alpha.encode message.algoId
    ++ (Alpha.encode message.clientCode
    ++ (Alpha.encode message.cpCode
    ++ (Alpha.encode message.freeText3
    ++ (Alpha.encode message.pad4
    ++ (encodeMany FillsGrpComp.encode message.fillsGrpComp.val
    ++ (encodeMany InstrmntLegExecGrpComp.encode message.instrmntLegExecGrpComp.val))))))))))))))))))))))))))))))))))

-- a long run of fields nests deeper than the elaborator's default limit
set_option maxRecDepth 4096 in
def decode (bytes : List UInt8) : Option (OrderExecNotification × List UInt8) := do
  let (filler4, bytes) ← Alpha.decode 2 bytes
  let (rbcHeaderMeComp, bytes) ← RbcHeaderMeComp.decode bytes
  let (orderId, bytes) ← decodeUIntLE 8 bytes
  let (senderLocationId, bytes) ← decodeUIntLE 8 bytes
  let (clOrdId, bytes) ← decodeUIntLE 8 bytes
  let (origClOrdId, bytes) ← decodeUIntLE 8 bytes
  let (securityId, bytes) ← decodeUIntLE 8 bytes
  let (execId, bytes) ← decodeUIntLE 8 bytes
  let (activityTime, bytes) ← decodeUIntLE 8 bytes
  let (filler1, bytes) ← Alpha.decode 8 bytes
  let (filler2, bytes) ← Alpha.decode 4 bytes
  let (messageTag, bytes) ← decodeUIntLE 4 bytes
  let (marketSegmentId, bytes) ← decodeUIntLE 4 bytes
  let (leavesQty, bytes) ← decodeUIntLE 4 bytes
  let (cumQty, bytes) ← decodeUIntLE 4 bytes
  let (cxlQty, bytes) ← decodeUIntLE 4 bytes
  let (noLegExecs, bytes) ← decodeUIntLE 2 bytes
  let (filler4v2, bytes) ← Alpha.decode 2 bytes
  let (execRestatementReason, bytes) ← decodeUIntLE 2 bytes
  let (accountType, bytes) ← decodeUInt 1 bytes
  let (productComplex, bytes) ← decodeUInt 1 bytes
  let (ordStatus, bytes) ← OrdStatus.decode bytes
  let (execType, bytes) ← ExecType.decode bytes
  let (triggered, bytes) ← decodeUInt 1 bytes
  let (noFills, bytes) ← decodeUInt 1 bytes
  let (side, bytes) ← decodeUInt 1 bytes
  let (rolloverFlag, bytes) ← decodeUInt 1 bytes
  let (account, bytes) ← Alpha.decode 2 bytes
  let (algoId, bytes) ← Alpha.decode 16 bytes
  let (clientCode, bytes) ← Alpha.decode 12 bytes
  let (cpCode, bytes) ← Alpha.decode 12 bytes
  let (freeText3, bytes) ← Alpha.decode 12 bytes
  let (pad4, bytes) ← Alpha.decode 4 bytes
  let (fillsGrpComp_, bytes) ← decodeMany FillsGrpComp.decode noFills.toNat bytes
  let (instrmntLegExecGrpComp_, bytes) ← decodeMany InstrmntLegExecGrpComp.decode noLegExecs.toNat bytes
  if fits_fillsGrpComp : fillsGrpComp_.length < 256 ^ 1 then
    if fits_instrmntLegExecGrpComp : instrmntLegExecGrpComp_.length < 256 ^ 2 then
      pure ({ filler4, rbcHeaderMeComp, orderId, senderLocationId, clOrdId, origClOrdId, securityId, execId, activityTime, filler1, filler2, messageTag, marketSegmentId, leavesQty, cumQty, cxlQty, filler4v2, execRestatementReason, accountType, productComplex, ordStatus, execType, triggered, side, rolloverFlag, account, algoId, clientCode, cpCode, freeText3, pad4, fillsGrpComp := ⟨fillsGrpComp_, fits_fillsGrpComp⟩, instrmntLegExecGrpComp := ⟨instrmntLegExecGrpComp_, fits_instrmntLegExecGrpComp⟩ }, bytes)
    else none
  else none

theorem encode_length_pos (message : OrderExecNotification) : (encode message).length > 0 := by
  unfold encode
  simp only [Alpha.encode_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : OrderExecNotification) : (encode message).length ≤ 2107530 := by
  have bound_fillsGrpComp := message.fillsGrpComp.length_lt
  have bound_instrmntLegExecGrpComp := message.instrmntLegExecGrpComp.length_lt
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, Alpha.encode_length, RbcHeaderMeComp.encode_length, encodeUIntLE_length, encodeUInt_length, OrdStatus.encode_length, ExecType.encode_length, encodeMany_length_const FillsGrpComp.encode 40 FillsGrpComp.encode_length, encodeMany_length_const InstrmntLegExecGrpComp.encode 32 InstrmntLegExecGrpComp.encode_length]
  omega

set_option maxRecDepth 4096 in
@[simp] theorem decode_encode (message : OrderExecNotification) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, RbcHeaderMeComp.decode_encode, some_bind]
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
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
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
  rw [List.append_assoc, decodeMany_bounded 1 FillsGrpComp.encode FillsGrpComp.decode FillsGrpComp.decode_encode, some_bind]
  dsimp only
  rw [decodeMany_bounded 2 InstrmntLegExecGrpComp.encode InstrmntLegExecGrpComp.decode InstrmntLegExecGrpComp.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.fillsGrpComp.length_lt, dite_eq_left message.instrmntLegExecGrpComp.length_lt]
  rfl

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : OrderExecNotification) : decode (encode message) = some (message, []) :=
  List.append_nil (encode message) ▸ decode_encode message []

end OrderExecNotification

/-- Leg Ord Grp Comp: 8 bytes -/
structure LegOrdGrpComp where
  legAccount : Alpha 2
  legPositionEffect : Alpha 1
  pad5 : Alpha 5
  deriving DecidableEq, Repr

namespace LegOrdGrpComp

def encode (message : LegOrdGrpComp) : List UInt8 :=
  Alpha.encode message.legAccount
    ++ (Alpha.encode message.legPositionEffect
    ++ (Alpha.encode message.pad5))

def decode (bytes : List UInt8) : Option (LegOrdGrpComp × List UInt8) := do
  let (legAccount, bytes) ← Alpha.decode 2 bytes
  let (legPositionEffect, bytes) ← Alpha.decode 1 bytes
  let (pad5, bytes) ← Alpha.decode 5 bytes
  pure ({ legAccount, legPositionEffect, pad5 }, bytes)

@[simp] theorem encode_length (message : LegOrdGrpComp) : (encode message).length = 8 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length]

theorem encode_length_pos (message : LegOrdGrpComp) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : LegOrdGrpComp) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end LegOrdGrpComp

/-- Order Exec Report Broadcast -/
structure OrderExecReportBroadcast where
  filler4 : Alpha 2
  rbcHeaderMeComp : RbcHeaderMeComp
  orderId : BitVec 64
  clOrdId : BitVec 64
  origClOrdId : BitVec 64
  securityId : BitVec 64
  maxPricePercentage : BitVec 64
  senderLocationId : BitVec 64
  execId : BitVec 64
  trdRegTsEntryTime : BitVec 64
  trdRegTsTimePriority : BitVec 64
  price : BitVec 64
  stopPx : BitVec 64
  underlyingDirtyPrice : BitVec 64
  yield : BitVec 64
  activityTime : BitVec 64
  filler1 : Alpha 8
  filler2 : Alpha 4
  marketSegmentId : BitVec 32
  messageTag : BitVec 32
  leavesQty : BitVec 32
  maxShow : BitVec 32
  cumQty : BitVec 32
  cxlQty : BitVec 32
  orderQty : BitVec 32
  expireDate : BitVec 32
  partyIdExecutingUnit : BitVec 32
  partyIdSessionId : BitVec 32
  partyIdExecutingTrader : BitVec 32
  partyIdEnteringTrader : BitVec 32
  filler4v2 : Alpha 2
  execRestatementReason : BitVec 16
  accountType : BitVec 8
  partyIdEnteringFirm : BitVec 8
  productComplex : BitVec 8
  ordStatus : OrdStatus
  execType : ExecType
  side : BitVec 8
  ordType : BitVec 8
  tradingCapacity : BitVec 8
  timeInForce : BitVec 8
  execInst : BitVec 8
  tradingSessionSubId : BitVec 8
  applSeqIndicator : BitVec 8
  stpcFlag : BitVec 8
  rolloverFlag : BitVec 8
  account : Alpha 2
  positionEffect : Alpha 1
  partyIdTakeUpTradingFirm : Alpha 5
  partyIdOrderOriginationFirm : Alpha 7
  partyIdBeneficiary : Alpha 9
  partyIdLocationId : Alpha 2
  custOrderHandlingInst : Alpha 1
  regulatoryText : Alpha 20
  algoId : Alpha 16
  clientCode : Alpha 12
  cpCode : Alpha 12
  freeText3 : Alpha 12
  triggered : BitVec 8
  pad2 : Alpha 2
  legOrdGrpComp : Bounded 1 LegOrdGrpComp
  fillsGrpComp : Bounded 1 FillsGrpComp
  instrmntLegExecGrpComp : Bounded 2 InstrmntLegExecGrpComp
  deriving DecidableEq, Repr

namespace OrderExecReportBroadcast

def encode (message : OrderExecReportBroadcast) : List UInt8 :=
  Alpha.encode message.filler4
    ++ (RbcHeaderMeComp.encode message.rbcHeaderMeComp
    ++ (encodeUIntLE 8 message.orderId
    ++ (encodeUIntLE 8 message.clOrdId
    ++ (encodeUIntLE 8 message.origClOrdId
    ++ (encodeUIntLE 8 message.securityId
    ++ (encodeUIntLE 8 message.maxPricePercentage
    ++ (encodeUIntLE 8 message.senderLocationId
    ++ (encodeUIntLE 8 message.execId
    ++ (encodeUIntLE 8 message.trdRegTsEntryTime
    ++ (encodeUIntLE 8 message.trdRegTsTimePriority
    ++ (encodeUIntLE 8 message.price
    ++ (encodeUIntLE 8 message.stopPx
    ++ (encodeUIntLE 8 message.underlyingDirtyPrice
    ++ (encodeUIntLE 8 message.yield
    ++ (encodeUIntLE 8 message.activityTime
    ++ (Alpha.encode message.filler1
    ++ (Alpha.encode message.filler2
    ++ (encodeUIntLE 4 message.marketSegmentId
    ++ (encodeUIntLE 4 message.messageTag
    ++ (encodeUIntLE 4 message.leavesQty
    ++ (encodeUIntLE 4 message.maxShow
    ++ (encodeUIntLE 4 message.cumQty
    ++ (encodeUIntLE 4 message.cxlQty
    ++ (encodeUIntLE 4 message.orderQty
    ++ (encodeUIntLE 4 message.expireDate
    ++ (encodeUIntLE 4 message.partyIdExecutingUnit
    ++ (encodeUIntLE 4 message.partyIdSessionId
    ++ (encodeUIntLE 4 message.partyIdExecutingTrader
    ++ (encodeUIntLE 4 message.partyIdEnteringTrader
    ++ (Alpha.encode message.filler4v2
    ++ (encodeUIntLE 2 (BitVec.ofNat (8 * 2) message.instrmntLegExecGrpComp.val.length)
    ++ (encodeUIntLE 2 message.execRestatementReason
    ++ (encodeUInt 1 message.accountType
    ++ (encodeUInt 1 message.partyIdEnteringFirm
    ++ (encodeUInt 1 message.productComplex
    ++ (OrdStatus.encode message.ordStatus
    ++ (ExecType.encode message.execType
    ++ (encodeUInt 1 message.side
    ++ (encodeUInt 1 message.ordType
    ++ (encodeUInt 1 message.tradingCapacity
    ++ (encodeUInt 1 message.timeInForce
    ++ (encodeUInt 1 message.execInst
    ++ (encodeUInt 1 message.tradingSessionSubId
    ++ (encodeUInt 1 message.applSeqIndicator
    ++ (encodeUInt 1 message.stpcFlag
    ++ (encodeUInt 1 message.rolloverFlag
    ++ (Alpha.encode message.account
    ++ (Alpha.encode message.positionEffect
    ++ (Alpha.encode message.partyIdTakeUpTradingFirm
    ++ (Alpha.encode message.partyIdOrderOriginationFirm
    ++ (Alpha.encode message.partyIdBeneficiary
    ++ (Alpha.encode message.partyIdLocationId
    ++ (Alpha.encode message.custOrderHandlingInst
    ++ (Alpha.encode message.regulatoryText
    ++ (Alpha.encode message.algoId
    ++ (Alpha.encode message.clientCode
    ++ (Alpha.encode message.cpCode
    ++ (Alpha.encode message.freeText3
    ++ (encodeUInt 1 (BitVec.ofNat (8 * 1) message.fillsGrpComp.val.length)
    ++ (encodeUInt 1 (BitVec.ofNat (8 * 1) message.legOrdGrpComp.val.length)
    ++ (encodeUInt 1 message.triggered
    ++ (Alpha.encode message.pad2
    ++ (encodeMany LegOrdGrpComp.encode message.legOrdGrpComp.val
    ++ (encodeMany FillsGrpComp.encode message.fillsGrpComp.val
    ++ (encodeMany InstrmntLegExecGrpComp.encode message.instrmntLegExecGrpComp.val)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

-- a long run of fields nests deeper than the elaborator's default limit
set_option maxRecDepth 4096 in
def decode (bytes : List UInt8) : Option (OrderExecReportBroadcast × List UInt8) := do
  let (filler4, bytes) ← Alpha.decode 2 bytes
  let (rbcHeaderMeComp, bytes) ← RbcHeaderMeComp.decode bytes
  let (orderId, bytes) ← decodeUIntLE 8 bytes
  let (clOrdId, bytes) ← decodeUIntLE 8 bytes
  let (origClOrdId, bytes) ← decodeUIntLE 8 bytes
  let (securityId, bytes) ← decodeUIntLE 8 bytes
  let (maxPricePercentage, bytes) ← decodeUIntLE 8 bytes
  let (senderLocationId, bytes) ← decodeUIntLE 8 bytes
  let (execId, bytes) ← decodeUIntLE 8 bytes
  let (trdRegTsEntryTime, bytes) ← decodeUIntLE 8 bytes
  let (trdRegTsTimePriority, bytes) ← decodeUIntLE 8 bytes
  let (price, bytes) ← decodeUIntLE 8 bytes
  let (stopPx, bytes) ← decodeUIntLE 8 bytes
  let (underlyingDirtyPrice, bytes) ← decodeUIntLE 8 bytes
  let (yield, bytes) ← decodeUIntLE 8 bytes
  let (activityTime, bytes) ← decodeUIntLE 8 bytes
  let (filler1, bytes) ← Alpha.decode 8 bytes
  let (filler2, bytes) ← Alpha.decode 4 bytes
  let (marketSegmentId, bytes) ← decodeUIntLE 4 bytes
  let (messageTag, bytes) ← decodeUIntLE 4 bytes
  let (leavesQty, bytes) ← decodeUIntLE 4 bytes
  let (maxShow, bytes) ← decodeUIntLE 4 bytes
  let (cumQty, bytes) ← decodeUIntLE 4 bytes
  let (cxlQty, bytes) ← decodeUIntLE 4 bytes
  let (orderQty, bytes) ← decodeUIntLE 4 bytes
  let (expireDate, bytes) ← decodeUIntLE 4 bytes
  let (partyIdExecutingUnit, bytes) ← decodeUIntLE 4 bytes
  let (partyIdSessionId, bytes) ← decodeUIntLE 4 bytes
  let (partyIdExecutingTrader, bytes) ← decodeUIntLE 4 bytes
  let (partyIdEnteringTrader, bytes) ← decodeUIntLE 4 bytes
  let (filler4v2, bytes) ← Alpha.decode 2 bytes
  let (noLegExecs, bytes) ← decodeUIntLE 2 bytes
  let (execRestatementReason, bytes) ← decodeUIntLE 2 bytes
  let (accountType, bytes) ← decodeUInt 1 bytes
  let (partyIdEnteringFirm, bytes) ← decodeUInt 1 bytes
  let (productComplex, bytes) ← decodeUInt 1 bytes
  let (ordStatus, bytes) ← OrdStatus.decode bytes
  let (execType, bytes) ← ExecType.decode bytes
  let (side, bytes) ← decodeUInt 1 bytes
  let (ordType, bytes) ← decodeUInt 1 bytes
  let (tradingCapacity, bytes) ← decodeUInt 1 bytes
  let (timeInForce, bytes) ← decodeUInt 1 bytes
  let (execInst, bytes) ← decodeUInt 1 bytes
  let (tradingSessionSubId, bytes) ← decodeUInt 1 bytes
  let (applSeqIndicator, bytes) ← decodeUInt 1 bytes
  let (stpcFlag, bytes) ← decodeUInt 1 bytes
  let (rolloverFlag, bytes) ← decodeUInt 1 bytes
  let (account, bytes) ← Alpha.decode 2 bytes
  let (positionEffect, bytes) ← Alpha.decode 1 bytes
  let (partyIdTakeUpTradingFirm, bytes) ← Alpha.decode 5 bytes
  let (partyIdOrderOriginationFirm, bytes) ← Alpha.decode 7 bytes
  let (partyIdBeneficiary, bytes) ← Alpha.decode 9 bytes
  let (partyIdLocationId, bytes) ← Alpha.decode 2 bytes
  let (custOrderHandlingInst, bytes) ← Alpha.decode 1 bytes
  let (regulatoryText, bytes) ← Alpha.decode 20 bytes
  let (algoId, bytes) ← Alpha.decode 16 bytes
  let (clientCode, bytes) ← Alpha.decode 12 bytes
  let (cpCode, bytes) ← Alpha.decode 12 bytes
  let (freeText3, bytes) ← Alpha.decode 12 bytes
  let (noFills, bytes) ← decodeUInt 1 bytes
  let (noLegs, bytes) ← decodeUInt 1 bytes
  let (triggered, bytes) ← decodeUInt 1 bytes
  let (pad2, bytes) ← Alpha.decode 2 bytes
  let (legOrdGrpComp_, bytes) ← decodeMany LegOrdGrpComp.decode noLegs.toNat bytes
  let (fillsGrpComp_, bytes) ← decodeMany FillsGrpComp.decode noFills.toNat bytes
  let (instrmntLegExecGrpComp_, bytes) ← decodeMany InstrmntLegExecGrpComp.decode noLegExecs.toNat bytes
  if fits_legOrdGrpComp : legOrdGrpComp_.length < 256 ^ 1 then
    if fits_fillsGrpComp : fillsGrpComp_.length < 256 ^ 1 then
      if fits_instrmntLegExecGrpComp : instrmntLegExecGrpComp_.length < 256 ^ 2 then
        pure ({ filler4, rbcHeaderMeComp, orderId, clOrdId, origClOrdId, securityId, maxPricePercentage, senderLocationId, execId, trdRegTsEntryTime, trdRegTsTimePriority, price, stopPx, underlyingDirtyPrice, yield, activityTime, filler1, filler2, marketSegmentId, messageTag, leavesQty, maxShow, cumQty, cxlQty, orderQty, expireDate, partyIdExecutingUnit, partyIdSessionId, partyIdExecutingTrader, partyIdEnteringTrader, filler4v2, execRestatementReason, accountType, partyIdEnteringFirm, productComplex, ordStatus, execType, side, ordType, tradingCapacity, timeInForce, execInst, tradingSessionSubId, applSeqIndicator, stpcFlag, rolloverFlag, account, positionEffect, partyIdTakeUpTradingFirm, partyIdOrderOriginationFirm, partyIdBeneficiary, partyIdLocationId, custOrderHandlingInst, regulatoryText, algoId, clientCode, cpCode, freeText3, triggered, pad2, legOrdGrpComp := ⟨legOrdGrpComp_, fits_legOrdGrpComp⟩, fillsGrpComp := ⟨fillsGrpComp_, fits_fillsGrpComp⟩, instrmntLegExecGrpComp := ⟨instrmntLegExecGrpComp_, fits_instrmntLegExecGrpComp⟩ }, bytes)
      else none
    else none
  else none

theorem encode_length_pos (message : OrderExecReportBroadcast) : (encode message).length > 0 := by
  unfold encode
  simp only [Alpha.encode_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : OrderExecReportBroadcast) : (encode message).length ≤ 2109706 := by
  have bound_legOrdGrpComp := message.legOrdGrpComp.length_lt
  have bound_fillsGrpComp := message.fillsGrpComp.length_lt
  have bound_instrmntLegExecGrpComp := message.instrmntLegExecGrpComp.length_lt
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, Alpha.encode_length, RbcHeaderMeComp.encode_length, encodeUIntLE_length, encodeUInt_length, OrdStatus.encode_length, ExecType.encode_length, encodeMany_length_const LegOrdGrpComp.encode 8 LegOrdGrpComp.encode_length, encodeMany_length_const FillsGrpComp.encode 40 FillsGrpComp.encode_length, encodeMany_length_const InstrmntLegExecGrpComp.encode 32 InstrmntLegExecGrpComp.encode_length]
  omega

set_option maxRecDepth 4096 in
@[simp] theorem decode_encode (message : OrderExecReportBroadcast) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, RbcHeaderMeComp.decode_encode, some_bind]
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
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
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
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeMany_bounded 1 LegOrdGrpComp.encode LegOrdGrpComp.decode LegOrdGrpComp.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeMany_bounded 1 FillsGrpComp.encode FillsGrpComp.decode FillsGrpComp.decode_encode, some_bind]
  dsimp only
  rw [decodeMany_bounded 2 InstrmntLegExecGrpComp.encode InstrmntLegExecGrpComp.decode InstrmntLegExecGrpComp.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.legOrdGrpComp.length_lt, dite_eq_left message.fillsGrpComp.length_lt, dite_eq_left message.instrmntLegExecGrpComp.length_lt]
  rfl

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : OrderExecReportBroadcast) : decode (encode message) = some (message, []) :=
  List.append_nil (encode message) ▸ decode_encode message []

end OrderExecReportBroadcast

/-- Order Exec Response -/
structure OrderExecResponse where
  filler4 : Alpha 2
  responseHeaderMeComp : ResponseHeaderMeComp
  orderId : BitVec 64
  clOrdId : BitVec 64
  origClOrdId : BitVec 64
  securityId : BitVec 64
  execId : BitVec 64
  trdRegTsEntryTime : BitVec 64
  trdRegTsTimePriority : BitVec 64
  activityTime : BitVec 64
  price : BitVec 64
  filler2 : Alpha 4
  marketSegmentId : BitVec 32
  leavesQty : BitVec 32
  cumQty : BitVec 32
  cxlQty : BitVec 32
  filler4v2 : Alpha 2
  execRestatementReason : BitVec 16
  productComplex : BitVec 8
  ordStatus : OrdStatus
  execType : ExecType
  triggered : BitVec 8
  rolloverFlag : BitVec 8
  algoId : Alpha 16
  fillsGrpComp : Bounded 1 FillsGrpComp
  instrmntLegExecGrpComp : Bounded 2 InstrmntLegExecGrpComp
  deriving DecidableEq, Repr

namespace OrderExecResponse

def encode (message : OrderExecResponse) : List UInt8 :=
  Alpha.encode message.filler4
    ++ (ResponseHeaderMeComp.encode message.responseHeaderMeComp
    ++ (encodeUIntLE 8 message.orderId
    ++ (encodeUIntLE 8 message.clOrdId
    ++ (encodeUIntLE 8 message.origClOrdId
    ++ (encodeUIntLE 8 message.securityId
    ++ (encodeUIntLE 8 message.execId
    ++ (encodeUIntLE 8 message.trdRegTsEntryTime
    ++ (encodeUIntLE 8 message.trdRegTsTimePriority
    ++ (encodeUIntLE 8 message.activityTime
    ++ (encodeUIntLE 8 message.price
    ++ (Alpha.encode message.filler2
    ++ (encodeUIntLE 4 message.marketSegmentId
    ++ (encodeUIntLE 4 message.leavesQty
    ++ (encodeUIntLE 4 message.cumQty
    ++ (encodeUIntLE 4 message.cxlQty
    ++ (Alpha.encode message.filler4v2
    ++ (encodeUIntLE 2 (BitVec.ofNat (8 * 2) message.instrmntLegExecGrpComp.val.length)
    ++ (encodeUIntLE 2 message.execRestatementReason
    ++ (encodeUInt 1 message.productComplex
    ++ (OrdStatus.encode message.ordStatus
    ++ (ExecType.encode message.execType
    ++ (encodeUInt 1 message.triggered
    ++ (encodeUInt 1 message.rolloverFlag
    ++ (encodeUInt 1 (BitVec.ofNat (8 * 1) message.fillsGrpComp.val.length)
    ++ (Alpha.encode message.algoId
    ++ (encodeMany FillsGrpComp.encode message.fillsGrpComp.val
    ++ (encodeMany InstrmntLegExecGrpComp.encode message.instrmntLegExecGrpComp.val)))))))))))))))))))))))))))

-- a long run of fields nests deeper than the elaborator's default limit
set_option maxRecDepth 4096 in
def decode (bytes : List UInt8) : Option (OrderExecResponse × List UInt8) := do
  let (filler4, bytes) ← Alpha.decode 2 bytes
  let (responseHeaderMeComp, bytes) ← ResponseHeaderMeComp.decode bytes
  let (orderId, bytes) ← decodeUIntLE 8 bytes
  let (clOrdId, bytes) ← decodeUIntLE 8 bytes
  let (origClOrdId, bytes) ← decodeUIntLE 8 bytes
  let (securityId, bytes) ← decodeUIntLE 8 bytes
  let (execId, bytes) ← decodeUIntLE 8 bytes
  let (trdRegTsEntryTime, bytes) ← decodeUIntLE 8 bytes
  let (trdRegTsTimePriority, bytes) ← decodeUIntLE 8 bytes
  let (activityTime, bytes) ← decodeUIntLE 8 bytes
  let (price, bytes) ← decodeUIntLE 8 bytes
  let (filler2, bytes) ← Alpha.decode 4 bytes
  let (marketSegmentId, bytes) ← decodeUIntLE 4 bytes
  let (leavesQty, bytes) ← decodeUIntLE 4 bytes
  let (cumQty, bytes) ← decodeUIntLE 4 bytes
  let (cxlQty, bytes) ← decodeUIntLE 4 bytes
  let (filler4v2, bytes) ← Alpha.decode 2 bytes
  let (noLegExecs, bytes) ← decodeUIntLE 2 bytes
  let (execRestatementReason, bytes) ← decodeUIntLE 2 bytes
  let (productComplex, bytes) ← decodeUInt 1 bytes
  let (ordStatus, bytes) ← OrdStatus.decode bytes
  let (execType, bytes) ← ExecType.decode bytes
  let (triggered, bytes) ← decodeUInt 1 bytes
  let (rolloverFlag, bytes) ← decodeUInt 1 bytes
  let (noFills, bytes) ← decodeUInt 1 bytes
  let (algoId, bytes) ← Alpha.decode 16 bytes
  let (fillsGrpComp_, bytes) ← decodeMany FillsGrpComp.decode noFills.toNat bytes
  let (instrmntLegExecGrpComp_, bytes) ← decodeMany InstrmntLegExecGrpComp.decode noLegExecs.toNat bytes
  if fits_fillsGrpComp : fillsGrpComp_.length < 256 ^ 1 then
    if fits_instrmntLegExecGrpComp : instrmntLegExecGrpComp_.length < 256 ^ 2 then
      pure ({ filler4, responseHeaderMeComp, orderId, clOrdId, origClOrdId, securityId, execId, trdRegTsEntryTime, trdRegTsTimePriority, activityTime, price, filler2, marketSegmentId, leavesQty, cumQty, cxlQty, filler4v2, execRestatementReason, productComplex, ordStatus, execType, triggered, rolloverFlag, algoId, fillsGrpComp := ⟨fillsGrpComp_, fits_fillsGrpComp⟩, instrmntLegExecGrpComp := ⟨instrmntLegExecGrpComp_, fits_instrmntLegExecGrpComp⟩ }, bytes)
    else none
  else none

theorem encode_length_pos (message : OrderExecResponse) : (encode message).length > 0 := by
  unfold encode
  simp only [Alpha.encode_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : OrderExecResponse) : (encode message).length ≤ 2107514 := by
  have bound_fillsGrpComp := message.fillsGrpComp.length_lt
  have bound_instrmntLegExecGrpComp := message.instrmntLegExecGrpComp.length_lt
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, Alpha.encode_length, ResponseHeaderMeComp.encode_length, encodeUIntLE_length, encodeUInt_length, OrdStatus.encode_length, ExecType.encode_length, encodeMany_length_const FillsGrpComp.encode 40 FillsGrpComp.encode_length, encodeMany_length_const InstrmntLegExecGrpComp.encode 32 InstrmntLegExecGrpComp.encode_length]
  omega

set_option maxRecDepth 4096 in
@[simp] theorem decode_encode (message : OrderExecResponse) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, ResponseHeaderMeComp.decode_encode, some_bind]
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
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeMany_bounded 1 FillsGrpComp.encode FillsGrpComp.decode FillsGrpComp.decode_encode, some_bind]
  dsimp only
  rw [decodeMany_bounded 2 InstrmntLegExecGrpComp.encode InstrmntLegExecGrpComp.decode InstrmntLegExecGrpComp.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.fillsGrpComp.length_lt, dite_eq_left message.instrmntLegExecGrpComp.length_lt]
  rfl

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : OrderExecResponse) : decode (encode message) = some (message, []) :=
  List.append_nil (encode message) ▸ decode_encode message []

end OrderExecResponse

/-- Quote Event Grp Comp: 104 bytes -/
structure QuoteEventGrpComp where
  orderId : BitVec 64
  senderLocationId : BitVec 64
  securityId : BitVec 64
  quoteEventPx : BitVec 64
  quoteMsgId : BitVec 64
  quoteEventMatchId : BitVec 32
  messageTag : BitVec 32
  quoteEventExecId : BitVec 32
  quoteEventQty : BitVec 32
  quoteEventType : BitVec 8
  quoteEventSide : BitVec 8
  quoteEventLiquidityInd : BitVec 8
  quoteEventReason : BitVec 8
  accountType : BitVec 8
  algoId : Alpha 16
  clientCode : Alpha 12
  cpCode : Alpha 12
  pad3 : Alpha 3
  deriving DecidableEq, Repr

namespace QuoteEventGrpComp

def encode (message : QuoteEventGrpComp) : List UInt8 :=
  encodeUIntLE 8 message.orderId
    ++ (encodeUIntLE 8 message.senderLocationId
    ++ (encodeUIntLE 8 message.securityId
    ++ (encodeUIntLE 8 message.quoteEventPx
    ++ (encodeUIntLE 8 message.quoteMsgId
    ++ (encodeUIntLE 4 message.quoteEventMatchId
    ++ (encodeUIntLE 4 message.messageTag
    ++ (encodeUIntLE 4 message.quoteEventExecId
    ++ (encodeUIntLE 4 message.quoteEventQty
    ++ (encodeUInt 1 message.quoteEventType
    ++ (encodeUInt 1 message.quoteEventSide
    ++ (encodeUInt 1 message.quoteEventLiquidityInd
    ++ (encodeUInt 1 message.quoteEventReason
    ++ (encodeUInt 1 message.accountType
    ++ (Alpha.encode message.algoId
    ++ (Alpha.encode message.clientCode
    ++ (Alpha.encode message.cpCode
    ++ (Alpha.encode message.pad3)))))))))))))))))

def decode (bytes : List UInt8) : Option (QuoteEventGrpComp × List UInt8) := do
  let (orderId, bytes) ← decodeUIntLE 8 bytes
  let (senderLocationId, bytes) ← decodeUIntLE 8 bytes
  let (securityId, bytes) ← decodeUIntLE 8 bytes
  let (quoteEventPx, bytes) ← decodeUIntLE 8 bytes
  let (quoteMsgId, bytes) ← decodeUIntLE 8 bytes
  let (quoteEventMatchId, bytes) ← decodeUIntLE 4 bytes
  let (messageTag, bytes) ← decodeUIntLE 4 bytes
  let (quoteEventExecId, bytes) ← decodeUIntLE 4 bytes
  let (quoteEventQty, bytes) ← decodeUIntLE 4 bytes
  let (quoteEventType, bytes) ← decodeUInt 1 bytes
  let (quoteEventSide, bytes) ← decodeUInt 1 bytes
  let (quoteEventLiquidityInd, bytes) ← decodeUInt 1 bytes
  let (quoteEventReason, bytes) ← decodeUInt 1 bytes
  let (accountType, bytes) ← decodeUInt 1 bytes
  let (algoId, bytes) ← Alpha.decode 16 bytes
  let (clientCode, bytes) ← Alpha.decode 12 bytes
  let (cpCode, bytes) ← Alpha.decode 12 bytes
  let (pad3, bytes) ← Alpha.decode 3 bytes
  pure ({ orderId, senderLocationId, securityId, quoteEventPx, quoteMsgId, quoteEventMatchId, messageTag, quoteEventExecId, quoteEventQty, quoteEventType, quoteEventSide, quoteEventLiquidityInd, quoteEventReason, accountType, algoId, clientCode, cpCode, pad3 }, bytes)

@[simp] theorem encode_length (message : QuoteEventGrpComp) : (encode message).length = 104 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, encodeUInt_length, Alpha.encode_length]

theorem encode_length_pos (message : QuoteEventGrpComp) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : QuoteEventGrpComp) (rest : List UInt8) :
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
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end QuoteEventGrpComp

/-- Quote Exec Report Broadcast -/
structure QuoteExecReportBroadcast where
  filler4 : Alpha 2
  rbcHeaderMeComp : RbcHeaderMeComp
  execId : BitVec 64
  stpcFlag : BitVec 8
  pad6 : Alpha 6
  quoteEventGrpComp : Bounded 1 QuoteEventGrpComp
  deriving DecidableEq, Repr

namespace QuoteExecReportBroadcast

def encode (message : QuoteExecReportBroadcast) : List UInt8 :=
  Alpha.encode message.filler4
    ++ (RbcHeaderMeComp.encode message.rbcHeaderMeComp
    ++ (encodeUIntLE 8 message.execId
    ++ (encodeUInt 1 (BitVec.ofNat (8 * 1) message.quoteEventGrpComp.val.length)
    ++ (encodeUInt 1 message.stpcFlag
    ++ (Alpha.encode message.pad6
    ++ (encodeMany QuoteEventGrpComp.encode message.quoteEventGrpComp.val))))))

def decode (bytes : List UInt8) : Option (QuoteExecReportBroadcast × List UInt8) := do
  let (filler4, bytes) ← Alpha.decode 2 bytes
  let (rbcHeaderMeComp, bytes) ← RbcHeaderMeComp.decode bytes
  let (execId, bytes) ← decodeUIntLE 8 bytes
  let (noQuoteEvents, bytes) ← decodeUInt 1 bytes
  let (stpcFlag, bytes) ← decodeUInt 1 bytes
  let (pad6, bytes) ← Alpha.decode 6 bytes
  let (quoteEventGrpComp_, bytes) ← decodeMany QuoteEventGrpComp.decode noQuoteEvents.toNat bytes
  if fits_quoteEventGrpComp : quoteEventGrpComp_.length < 256 ^ 1 then
    pure ({ filler4, rbcHeaderMeComp, execId, stpcFlag, pad6, quoteEventGrpComp := ⟨quoteEventGrpComp_, fits_quoteEventGrpComp⟩ }, bytes)
  else none

theorem encode_length_pos (message : QuoteExecReportBroadcast) : (encode message).length > 0 := by
  unfold encode
  simp only [Alpha.encode_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : QuoteExecReportBroadcast) : (encode message).length ≤ 26586 := by
  have bound_quoteEventGrpComp := message.quoteEventGrpComp.length_lt
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, Alpha.encode_length, RbcHeaderMeComp.encode_length, encodeUIntLE_length, encodeUInt_length, encodeMany_length_const QuoteEventGrpComp.encode 104 QuoteEventGrpComp.encode_length]
  omega

@[simp] theorem decode_encode (message : QuoteExecReportBroadcast) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, RbcHeaderMeComp.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [decodeMany_bounded 1 QuoteEventGrpComp.encode QuoteEventGrpComp.decode QuoteEventGrpComp.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.quoteEventGrpComp.length_lt]
  rfl

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : QuoteExecReportBroadcast) : decode (encode message) = some (message, []) :=
  List.append_nil (encode message) ▸ decode_encode message []

end QuoteExecReportBroadcast

/-- Quote Leg Exec Grp Comp: 32 bytes -/
structure QuoteLegExecGrpComp where
  legSecurityId : BitVec 64
  legLastPx : BitVec 64
  legLastQty : BitVec 32
  legExecId : BitVec 32
  legSide : BitVec 8
  noQuoteEventsIndex : BitVec 8
  pad6 : Alpha 6
  deriving DecidableEq, Repr

namespace QuoteLegExecGrpComp

def encode (message : QuoteLegExecGrpComp) : List UInt8 :=
  encodeUIntLE 8 message.legSecurityId
    ++ (encodeUIntLE 8 message.legLastPx
    ++ (encodeUIntLE 4 message.legLastQty
    ++ (encodeUIntLE 4 message.legExecId
    ++ (encodeUInt 1 message.legSide
    ++ (encodeUInt 1 message.noQuoteEventsIndex
    ++ (Alpha.encode message.pad6))))))

def decode (bytes : List UInt8) : Option (QuoteLegExecGrpComp × List UInt8) := do
  let (legSecurityId, bytes) ← decodeUIntLE 8 bytes
  let (legLastPx, bytes) ← decodeUIntLE 8 bytes
  let (legLastQty, bytes) ← decodeUIntLE 4 bytes
  let (legExecId, bytes) ← decodeUIntLE 4 bytes
  let (legSide, bytes) ← decodeUInt 1 bytes
  let (noQuoteEventsIndex, bytes) ← decodeUInt 1 bytes
  let (pad6, bytes) ← Alpha.decode 6 bytes
  pure ({ legSecurityId, legLastPx, legLastQty, legExecId, legSide, noQuoteEventsIndex, pad6 }, bytes)

@[simp] theorem encode_length (message : QuoteLegExecGrpComp) : (encode message).length = 32 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, encodeUInt_length, Alpha.encode_length]

theorem encode_length_pos (message : QuoteLegExecGrpComp) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : QuoteLegExecGrpComp) (rest : List UInt8) :
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
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end QuoteLegExecGrpComp

/-- Quote Execution Report -/
structure QuoteExecutionReport where
  filler4 : Alpha 2
  rbcHeaderMeComp : RbcHeaderMeComp
  execId : BitVec 64
  marketSegmentId : BitVec 32
  stpcFlag : BitVec 8
  quoteEventGrpComp : Bounded 1 QuoteEventGrpComp
  quoteLegExecGrpComp : Bounded 2 QuoteLegExecGrpComp
  deriving DecidableEq, Repr

namespace QuoteExecutionReport

def encode (message : QuoteExecutionReport) : List UInt8 :=
  Alpha.encode message.filler4
    ++ (RbcHeaderMeComp.encode message.rbcHeaderMeComp
    ++ (encodeUIntLE 8 message.execId
    ++ (encodeUIntLE 4 message.marketSegmentId
    ++ (encodeUIntLE 2 (BitVec.ofNat (8 * 2) message.quoteLegExecGrpComp.val.length)
    ++ (encodeUInt 1 (BitVec.ofNat (8 * 1) message.quoteEventGrpComp.val.length)
    ++ (encodeUInt 1 message.stpcFlag
    ++ (encodeMany QuoteEventGrpComp.encode message.quoteEventGrpComp.val
    ++ (encodeMany QuoteLegExecGrpComp.encode message.quoteLegExecGrpComp.val))))))))

def decode (bytes : List UInt8) : Option (QuoteExecutionReport × List UInt8) := do
  let (filler4, bytes) ← Alpha.decode 2 bytes
  let (rbcHeaderMeComp, bytes) ← RbcHeaderMeComp.decode bytes
  let (execId, bytes) ← decodeUIntLE 8 bytes
  let (marketSegmentId, bytes) ← decodeUIntLE 4 bytes
  let (noLegExecs, bytes) ← decodeUIntLE 2 bytes
  let (noQuoteEvents, bytes) ← decodeUInt 1 bytes
  let (stpcFlag, bytes) ← decodeUInt 1 bytes
  let (quoteEventGrpComp_, bytes) ← decodeMany QuoteEventGrpComp.decode noQuoteEvents.toNat bytes
  let (quoteLegExecGrpComp_, bytes) ← decodeMany QuoteLegExecGrpComp.decode noLegExecs.toNat bytes
  if fits_quoteEventGrpComp : quoteEventGrpComp_.length < 256 ^ 1 then
    if fits_quoteLegExecGrpComp : quoteLegExecGrpComp_.length < 256 ^ 2 then
      pure ({ filler4, rbcHeaderMeComp, execId, marketSegmentId, stpcFlag, quoteEventGrpComp := ⟨quoteEventGrpComp_, fits_quoteEventGrpComp⟩, quoteLegExecGrpComp := ⟨quoteLegExecGrpComp_, fits_quoteLegExecGrpComp⟩ }, bytes)
    else none
  else none

theorem encode_length_pos (message : QuoteExecutionReport) : (encode message).length > 0 := by
  unfold encode
  simp only [Alpha.encode_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : QuoteExecutionReport) : (encode message).length ≤ 2123706 := by
  have bound_quoteEventGrpComp := message.quoteEventGrpComp.length_lt
  have bound_quoteLegExecGrpComp := message.quoteLegExecGrpComp.length_lt
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, Alpha.encode_length, RbcHeaderMeComp.encode_length, encodeUIntLE_length, encodeUInt_length, encodeMany_length_const QuoteEventGrpComp.encode 104 QuoteEventGrpComp.encode_length, encodeMany_length_const QuoteLegExecGrpComp.encode 32 QuoteLegExecGrpComp.encode_length]
  omega

@[simp] theorem decode_encode (message : QuoteExecutionReport) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, RbcHeaderMeComp.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeMany_bounded 1 QuoteEventGrpComp.encode QuoteEventGrpComp.decode QuoteEventGrpComp.decode_encode, some_bind]
  dsimp only
  rw [decodeMany_bounded 2 QuoteLegExecGrpComp.encode QuoteLegExecGrpComp.decode QuoteLegExecGrpComp.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.quoteEventGrpComp.length_lt, dite_eq_left message.quoteLegExecGrpComp.length_lt]
  rfl

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : QuoteExecutionReport) : decode (encode message) = some (message, []) :=
  List.append_nil (encode message) ▸ decode_encode message []

end QuoteExecutionReport

/-- Reject -/
structure Reject where
  filler4 : Alpha 2
  nrResponseHeaderMeComp : NrResponseHeaderMeComp
  sessionRejectReason : BitVec 32
  sessionStatus : BitVec 8
  pad1 : Alpha 1
  varText : Bounded 2 UInt8
  alignmentPadding : Capped 7
  deriving DecidableEq, Repr

namespace Reject

def encode (message : Reject) : List UInt8 :=
  Alpha.encode message.filler4
    ++ (NrResponseHeaderMeComp.encode message.nrResponseHeaderMeComp
    ++ (encodeUIntLE 4 message.sessionRejectReason
    ++ (encodeUIntLE 2 (BitVec.ofNat (8 * 2) message.varText.val.length)
    ++ (encodeUInt 1 message.sessionStatus
    ++ (Alpha.encode message.pad1
    ++ (encodeMany Byte.encode message.varText.val
    ++ (message.alignmentPadding.val)))))))

def decode (bytes : List UInt8) : Option Reject := do
  let (filler4, bytes) ← Alpha.decode 2 bytes
  let (nrResponseHeaderMeComp, bytes) ← NrResponseHeaderMeComp.decode bytes
  let (sessionRejectReason, bytes) ← decodeUIntLE 4 bytes
  let (varTextLen, bytes) ← decodeUIntLE 2 bytes
  let (sessionStatus, bytes) ← decodeUInt 1 bytes
  let (pad1, bytes) ← Alpha.decode 1 bytes
  let (varText_, bytes) ← decodeMany Byte.decode varTextLen.toNat bytes
  let alignmentPadding_ := bytes
  if fits_varText : varText_.length < 256 ^ 2 then
    if fits_alignmentPadding : alignmentPadding_.length ≤ 7 then
      pure { filler4, nrResponseHeaderMeComp, sessionRejectReason, sessionStatus, pad1, varText := ⟨varText_, fits_varText⟩, alignmentPadding := ⟨alignmentPadding_, fits_alignmentPadding⟩ }
    else none
  else none

theorem encode_length_pos (message : Reject) : (encode message).length > 0 := by
  unfold encode
  simp only [Alpha.encode_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : Reject) : (encode message).length ≤ 65608 := by
  have bound_varText := message.varText.length_lt
  have bound_alignmentPadding := message.alignmentPadding.length_le
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, Alpha.encode_length, NrResponseHeaderMeComp.encode_length, encodeUIntLE_length, encodeUInt_length, encodeMany_length_const Byte.encode 1 Byte.encode_length]
  omega

theorem decode_encode (message : Reject) : decode (encode message) = some message := by
  unfold decode encode
  rw [Alpha.decode_encode, some_bind]
  dsimp only
  rw [NrResponseHeaderMeComp.decode_encode, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  dsimp only
  rw [decodeMany_bounded 2 Byte.encode Byte.decode Byte.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.varText.length_lt, dite_eq_left message.alignmentPadding.length_le]
  rfl

end Reject

/-- Retransmit Me Message Response: 66 bytes -/
structure RetransmitMeMessageResponse where
  filler4 : Alpha 2
  responseHeaderComp : ResponseHeaderComp
  applTotalMessageCount : BitVec 16
  applEndMsgId : Alpha 16
  refApplLastMsgId : Alpha 16
  pad6 : Alpha 6
  deriving DecidableEq, Repr

namespace RetransmitMeMessageResponse

def encode (message : RetransmitMeMessageResponse) : List UInt8 :=
  Alpha.encode message.filler4
    ++ (ResponseHeaderComp.encode message.responseHeaderComp
    ++ (encodeUIntLE 2 message.applTotalMessageCount
    ++ (Alpha.encode message.applEndMsgId
    ++ (Alpha.encode message.refApplLastMsgId
    ++ (Alpha.encode message.pad6)))))

def decode (bytes : List UInt8) : Option (RetransmitMeMessageResponse × List UInt8) := do
  let (filler4, bytes) ← Alpha.decode 2 bytes
  let (responseHeaderComp, bytes) ← ResponseHeaderComp.decode bytes
  let (applTotalMessageCount, bytes) ← decodeUIntLE 2 bytes
  let (applEndMsgId, bytes) ← Alpha.decode 16 bytes
  let (refApplLastMsgId, bytes) ← Alpha.decode 16 bytes
  let (pad6, bytes) ← Alpha.decode 6 bytes
  pure ({ filler4, responseHeaderComp, applTotalMessageCount, applEndMsgId, refApplLastMsgId, pad6 }, bytes)

@[simp] theorem encode_length (message : RetransmitMeMessageResponse) : (encode message).length = 66 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, ResponseHeaderComp.encode_length, encodeUIntLE_length]

theorem encode_length_pos (message : RetransmitMeMessageResponse) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : RetransmitMeMessageResponse) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, ResponseHeaderComp.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : RetransmitMeMessageResponse) : decode (encode message) = some (message, []) :=
  List.append_nil (encode message) ▸ decode_encode message []

end RetransmitMeMessageResponse

/-- Retransmit Response: 50 bytes -/
structure RetransmitResponse where
  filler4 : Alpha 2
  responseHeaderComp : ResponseHeaderComp
  applEndSeqNum : BitVec 64
  refApplLastSeqNum : BitVec 64
  applTotalMessageCount : BitVec 16
  pad6 : Alpha 6
  deriving DecidableEq, Repr

namespace RetransmitResponse

def encode (message : RetransmitResponse) : List UInt8 :=
  Alpha.encode message.filler4
    ++ (ResponseHeaderComp.encode message.responseHeaderComp
    ++ (encodeUIntLE 8 message.applEndSeqNum
    ++ (encodeUIntLE 8 message.refApplLastSeqNum
    ++ (encodeUIntLE 2 message.applTotalMessageCount
    ++ (Alpha.encode message.pad6)))))

def decode (bytes : List UInt8) : Option (RetransmitResponse × List UInt8) := do
  let (filler4, bytes) ← Alpha.decode 2 bytes
  let (responseHeaderComp, bytes) ← ResponseHeaderComp.decode bytes
  let (applEndSeqNum, bytes) ← decodeUIntLE 8 bytes
  let (refApplLastSeqNum, bytes) ← decodeUIntLE 8 bytes
  let (applTotalMessageCount, bytes) ← decodeUIntLE 2 bytes
  let (pad6, bytes) ← Alpha.decode 6 bytes
  pure ({ filler4, responseHeaderComp, applEndSeqNum, refApplLastSeqNum, applTotalMessageCount, pad6 }, bytes)

@[simp] theorem encode_length (message : RetransmitResponse) : (encode message).length = 50 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, ResponseHeaderComp.encode_length, encodeUIntLE_length]

theorem encode_length_pos (message : RetransmitResponse) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : RetransmitResponse) (rest : List UInt8) :
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
  rw [Alpha.decode_encode, some_bind]
  rfl

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : RetransmitResponse) : decode (encode message) = some (message, []) :=
  List.append_nil (encode message) ▸ decode_encode message []

end RetransmitResponse

/-- Risk Collateral Alert Admin Broadcast -/
structure RiskCollateralAlertAdminBroadcast where
  filler4 : Alpha 2
  rbcHeaderComp : RbcHeaderComp
  totalCollateral : BitVec 64
  utilizedCollateral : BitVec 64
  unutilizedCollateral : BitVec 64
  origTime : BitVec 64
  percentageUtilized : BitVec 32
  marketSegmentId : BitVec 32
  marketId : BitVec 16
  rrmState : BitVec 8
  memberType : BitVec 8
  incrementDecrementStatus : BitVec 8
  segmentIndicator : BitVec 8
  duration : BitVec 8
  clientCode : Alpha 12
  businessUnitSymbol : Alpha 8
  pad3 : Alpha 3
  varText : Bounded 2 UInt8
  alignmentPadding : Capped 7
  deriving DecidableEq, Repr

namespace RiskCollateralAlertAdminBroadcast

def encode (message : RiskCollateralAlertAdminBroadcast) : List UInt8 :=
  Alpha.encode message.filler4
    ++ (RbcHeaderComp.encode message.rbcHeaderComp
    ++ (encodeUIntLE 8 message.totalCollateral
    ++ (encodeUIntLE 8 message.utilizedCollateral
    ++ (encodeUIntLE 8 message.unutilizedCollateral
    ++ (encodeUIntLE 8 message.origTime
    ++ (encodeUIntLE 4 message.percentageUtilized
    ++ (encodeUIntLE 4 message.marketSegmentId
    ++ (encodeUIntLE 2 message.marketId
    ++ (encodeUIntLE 2 (BitVec.ofNat (8 * 2) message.varText.val.length)
    ++ (encodeUInt 1 message.rrmState
    ++ (encodeUInt 1 message.memberType
    ++ (encodeUInt 1 message.incrementDecrementStatus
    ++ (encodeUInt 1 message.segmentIndicator
    ++ (encodeUInt 1 message.duration
    ++ (Alpha.encode message.clientCode
    ++ (Alpha.encode message.businessUnitSymbol
    ++ (Alpha.encode message.pad3
    ++ (encodeMany Byte.encode message.varText.val
    ++ (message.alignmentPadding.val)))))))))))))))))))

def decode (bytes : List UInt8) : Option RiskCollateralAlertAdminBroadcast := do
  let (filler4, bytes) ← Alpha.decode 2 bytes
  let (rbcHeaderComp, bytes) ← RbcHeaderComp.decode bytes
  let (totalCollateral, bytes) ← decodeUIntLE 8 bytes
  let (utilizedCollateral, bytes) ← decodeUIntLE 8 bytes
  let (unutilizedCollateral, bytes) ← decodeUIntLE 8 bytes
  let (origTime, bytes) ← decodeUIntLE 8 bytes
  let (percentageUtilized, bytes) ← decodeUIntLE 4 bytes
  let (marketSegmentId, bytes) ← decodeUIntLE 4 bytes
  let (marketId, bytes) ← decodeUIntLE 2 bytes
  let (varTextLen, bytes) ← decodeUIntLE 2 bytes
  let (rrmState, bytes) ← decodeUInt 1 bytes
  let (memberType, bytes) ← decodeUInt 1 bytes
  let (incrementDecrementStatus, bytes) ← decodeUInt 1 bytes
  let (segmentIndicator, bytes) ← decodeUInt 1 bytes
  let (duration, bytes) ← decodeUInt 1 bytes
  let (clientCode, bytes) ← Alpha.decode 12 bytes
  let (businessUnitSymbol, bytes) ← Alpha.decode 8 bytes
  let (pad3, bytes) ← Alpha.decode 3 bytes
  let (varText_, bytes) ← decodeMany Byte.decode varTextLen.toNat bytes
  let alignmentPadding_ := bytes
  if fits_varText : varText_.length < 256 ^ 2 then
    if fits_alignmentPadding : alignmentPadding_.length ≤ 7 then
      pure { filler4, rbcHeaderComp, totalCollateral, utilizedCollateral, unutilizedCollateral, origTime, percentageUtilized, marketSegmentId, marketId, rrmState, memberType, incrementDecrementStatus, segmentIndicator, duration, clientCode, businessUnitSymbol, pad3, varText := ⟨varText_, fits_varText⟩, alignmentPadding := ⟨alignmentPadding_, fits_alignmentPadding⟩ }
    else none
  else none

theorem encode_length_pos (message : RiskCollateralAlertAdminBroadcast) : (encode message).length > 0 := by
  unfold encode
  simp only [Alpha.encode_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : RiskCollateralAlertAdminBroadcast) : (encode message).length ≤ 65648 := by
  have bound_varText := message.varText.length_lt
  have bound_alignmentPadding := message.alignmentPadding.length_le
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, Alpha.encode_length, RbcHeaderComp.encode_length, encodeUIntLE_length, encodeUInt_length, encodeMany_length_const Byte.encode 1 Byte.encode_length]
  omega

theorem decode_encode (message : RiskCollateralAlertAdminBroadcast) : decode (encode message) = some message := by
  unfold decode encode
  rw [Alpha.decode_encode, some_bind]
  dsimp only
  rw [RbcHeaderComp.decode_encode, some_bind]
  dsimp only
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
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  dsimp only
  rw [decodeMany_bounded 2 Byte.encode Byte.decode Byte.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.varText.length_lt, dite_eq_left message.alignmentPadding.length_le]
  rfl

end RiskCollateralAlertAdminBroadcast

/-- Risk Collateral Alert Broadcast -/
structure RiskCollateralAlertBroadcast where
  filler4 : Alpha 2
  rbcHeaderComp : RbcHeaderComp
  origTime : BitVec 64
  percentageUtilized : BitVec 32
  marketSegmentId : BitVec 32
  marketId : BitVec 16
  rrmState : BitVec 8
  memberType : BitVec 8
  incrementDecrementStatus : BitVec 8
  segmentIndicator : BitVec 8
  duration : BitVec 8
  clientCode : Alpha 12
  businessUnitSymbol : Alpha 8
  pad3 : Alpha 3
  varText : Bounded 2 UInt8
  alignmentPadding : Capped 7
  deriving DecidableEq, Repr

namespace RiskCollateralAlertBroadcast

def encode (message : RiskCollateralAlertBroadcast) : List UInt8 :=
  Alpha.encode message.filler4
    ++ (RbcHeaderComp.encode message.rbcHeaderComp
    ++ (encodeUIntLE 8 message.origTime
    ++ (encodeUIntLE 4 message.percentageUtilized
    ++ (encodeUIntLE 4 message.marketSegmentId
    ++ (encodeUIntLE 2 message.marketId
    ++ (encodeUIntLE 2 (BitVec.ofNat (8 * 2) message.varText.val.length)
    ++ (encodeUInt 1 message.rrmState
    ++ (encodeUInt 1 message.memberType
    ++ (encodeUInt 1 message.incrementDecrementStatus
    ++ (encodeUInt 1 message.segmentIndicator
    ++ (encodeUInt 1 message.duration
    ++ (Alpha.encode message.clientCode
    ++ (Alpha.encode message.businessUnitSymbol
    ++ (Alpha.encode message.pad3
    ++ (encodeMany Byte.encode message.varText.val
    ++ (message.alignmentPadding.val))))))))))))))))

def decode (bytes : List UInt8) : Option RiskCollateralAlertBroadcast := do
  let (filler4, bytes) ← Alpha.decode 2 bytes
  let (rbcHeaderComp, bytes) ← RbcHeaderComp.decode bytes
  let (origTime, bytes) ← decodeUIntLE 8 bytes
  let (percentageUtilized, bytes) ← decodeUIntLE 4 bytes
  let (marketSegmentId, bytes) ← decodeUIntLE 4 bytes
  let (marketId, bytes) ← decodeUIntLE 2 bytes
  let (varTextLen, bytes) ← decodeUIntLE 2 bytes
  let (rrmState, bytes) ← decodeUInt 1 bytes
  let (memberType, bytes) ← decodeUInt 1 bytes
  let (incrementDecrementStatus, bytes) ← decodeUInt 1 bytes
  let (segmentIndicator, bytes) ← decodeUInt 1 bytes
  let (duration, bytes) ← decodeUInt 1 bytes
  let (clientCode, bytes) ← Alpha.decode 12 bytes
  let (businessUnitSymbol, bytes) ← Alpha.decode 8 bytes
  let (pad3, bytes) ← Alpha.decode 3 bytes
  let (varText_, bytes) ← decodeMany Byte.decode varTextLen.toNat bytes
  let alignmentPadding_ := bytes
  if fits_varText : varText_.length < 256 ^ 2 then
    if fits_alignmentPadding : alignmentPadding_.length ≤ 7 then
      pure { filler4, rbcHeaderComp, origTime, percentageUtilized, marketSegmentId, marketId, rrmState, memberType, incrementDecrementStatus, segmentIndicator, duration, clientCode, businessUnitSymbol, pad3, varText := ⟨varText_, fits_varText⟩, alignmentPadding := ⟨alignmentPadding_, fits_alignmentPadding⟩ }
    else none
  else none

theorem encode_length_pos (message : RiskCollateralAlertBroadcast) : (encode message).length > 0 := by
  unfold encode
  simp only [Alpha.encode_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : RiskCollateralAlertBroadcast) : (encode message).length ≤ 65624 := by
  have bound_varText := message.varText.length_lt
  have bound_alignmentPadding := message.alignmentPadding.length_le
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, Alpha.encode_length, RbcHeaderComp.encode_length, encodeUIntLE_length, encodeUInt_length, encodeMany_length_const Byte.encode 1 Byte.encode_length]
  omega

theorem decode_encode (message : RiskCollateralAlertBroadcast) : decode (encode message) = some message := by
  unfold decode encode
  rw [Alpha.decode_encode, some_bind]
  dsimp only
  rw [RbcHeaderComp.decode_encode, some_bind]
  dsimp only
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
  rw [decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  dsimp only
  rw [decodeMany_bounded 2 Byte.encode Byte.decode Byte.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.varText.length_lt, dite_eq_left message.alignmentPadding.length_le]
  rfl

end RiskCollateralAlertBroadcast

/-- Risk Notification Broadcast: 106 bytes -/
structure RiskNotificationBroadcast where
  filler4 : Alpha 2
  rbcHeaderComp : RbcHeaderComp
  transactTime : BitVec 64
  tradeDate : BitVec 32
  partyDetailIdExecutingUnit : BitVec 32
  requestingPartyIdExecutingSystem : BitVec 32
  marketSegmentId : BitVec 32
  marketId : BitVec 16
  riskModeStatus : BitVec 8
  segmentIndicator : BitVec 8
  listUpdateAction : ListUpdateAction
  riskLimitAction : BitVec 8
  scopeIdentifier : BitVec 8
  clientCode : Alpha 12
  requestingPartyEnteringFirm : Alpha 9
  requestingPartyClearingFirm : Alpha 9
  businessUnitSymbol : Alpha 8
  pad3 : Alpha 3
  deriving DecidableEq, Repr

namespace RiskNotificationBroadcast

def encode (message : RiskNotificationBroadcast) : List UInt8 :=
  Alpha.encode message.filler4
    ++ (RbcHeaderComp.encode message.rbcHeaderComp
    ++ (encodeUIntLE 8 message.transactTime
    ++ (encodeUIntLE 4 message.tradeDate
    ++ (encodeUIntLE 4 message.partyDetailIdExecutingUnit
    ++ (encodeUIntLE 4 message.requestingPartyIdExecutingSystem
    ++ (encodeUIntLE 4 message.marketSegmentId
    ++ (encodeUIntLE 2 message.marketId
    ++ (encodeUInt 1 message.riskModeStatus
    ++ (encodeUInt 1 message.segmentIndicator
    ++ (ListUpdateAction.encode message.listUpdateAction
    ++ (encodeUInt 1 message.riskLimitAction
    ++ (encodeUInt 1 message.scopeIdentifier
    ++ (Alpha.encode message.clientCode
    ++ (Alpha.encode message.requestingPartyEnteringFirm
    ++ (Alpha.encode message.requestingPartyClearingFirm
    ++ (Alpha.encode message.businessUnitSymbol
    ++ (Alpha.encode message.pad3)))))))))))))))))

def decode (bytes : List UInt8) : Option (RiskNotificationBroadcast × List UInt8) := do
  let (filler4, bytes) ← Alpha.decode 2 bytes
  let (rbcHeaderComp, bytes) ← RbcHeaderComp.decode bytes
  let (transactTime, bytes) ← decodeUIntLE 8 bytes
  let (tradeDate, bytes) ← decodeUIntLE 4 bytes
  let (partyDetailIdExecutingUnit, bytes) ← decodeUIntLE 4 bytes
  let (requestingPartyIdExecutingSystem, bytes) ← decodeUIntLE 4 bytes
  let (marketSegmentId, bytes) ← decodeUIntLE 4 bytes
  let (marketId, bytes) ← decodeUIntLE 2 bytes
  let (riskModeStatus, bytes) ← decodeUInt 1 bytes
  let (segmentIndicator, bytes) ← decodeUInt 1 bytes
  let (listUpdateAction, bytes) ← ListUpdateAction.decode bytes
  let (riskLimitAction, bytes) ← decodeUInt 1 bytes
  let (scopeIdentifier, bytes) ← decodeUInt 1 bytes
  let (clientCode, bytes) ← Alpha.decode 12 bytes
  let (requestingPartyEnteringFirm, bytes) ← Alpha.decode 9 bytes
  let (requestingPartyClearingFirm, bytes) ← Alpha.decode 9 bytes
  let (businessUnitSymbol, bytes) ← Alpha.decode 8 bytes
  let (pad3, bytes) ← Alpha.decode 3 bytes
  pure ({ filler4, rbcHeaderComp, transactTime, tradeDate, partyDetailIdExecutingUnit, requestingPartyIdExecutingSystem, marketSegmentId, marketId, riskModeStatus, segmentIndicator, listUpdateAction, riskLimitAction, scopeIdentifier, clientCode, requestingPartyEnteringFirm, requestingPartyClearingFirm, businessUnitSymbol, pad3 }, bytes)

@[simp] theorem encode_length (message : RiskNotificationBroadcast) : (encode message).length = 106 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, RbcHeaderComp.encode_length, encodeUIntLE_length, encodeUInt_length, ListUpdateAction.encode_length]

theorem encode_length_pos (message : RiskNotificationBroadcast) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : RiskNotificationBroadcast) (rest : List UInt8) :
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
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, ListUpdateAction.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
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
  rw [Alpha.decode_encode, some_bind]
  rfl

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : RiskNotificationBroadcast) : decode (encode message) = some (message, []) :=
  List.append_nil (encode message) ▸ decode_encode message []

end RiskNotificationBroadcast

/-- Nrbc Header Comp: 16 bytes -/
structure NrbcHeaderComp where
  sendingTime : BitVec 64
  applSubId : BitVec 32
  applId : BitVec 8
  lastFragment : BitVec 8
  pad2 : Alpha 2
  deriving DecidableEq, Repr

namespace NrbcHeaderComp

def encode (message : NrbcHeaderComp) : List UInt8 :=
  encodeUIntLE 8 message.sendingTime
    ++ (encodeUIntLE 4 message.applSubId
    ++ (encodeUInt 1 message.applId
    ++ (encodeUInt 1 message.lastFragment
    ++ (Alpha.encode message.pad2))))

def decode (bytes : List UInt8) : Option (NrbcHeaderComp × List UInt8) := do
  let (sendingTime, bytes) ← decodeUIntLE 8 bytes
  let (applSubId, bytes) ← decodeUIntLE 4 bytes
  let (applId, bytes) ← decodeUInt 1 bytes
  let (lastFragment, bytes) ← decodeUInt 1 bytes
  let (pad2, bytes) ← Alpha.decode 2 bytes
  pure ({ sendingTime, applSubId, applId, lastFragment, pad2 }, bytes)

@[simp] theorem encode_length (message : NrbcHeaderComp) : (encode message).length = 16 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, encodeUInt_length, Alpha.encode_length]

theorem encode_length_pos (message : NrbcHeaderComp) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : NrbcHeaderComp) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end NrbcHeaderComp

/-- Service Availability Broadcast: 42 bytes -/
structure ServiceAvailabilityBroadcast where
  filler4 : Alpha 2
  nrbcHeaderComp : NrbcHeaderComp
  matchingEngineTradeDate : BitVec 32
  tradeManagerTradeDate : BitVec 32
  applSeqTradeDate : BitVec 32
  partitionId : BitVec 16
  matchingEngineStatus : BitVec 8
  tradeManagerStatus : BitVec 8
  applSeqStatus : BitVec 8
  pad7 : Alpha 7
  deriving DecidableEq, Repr

namespace ServiceAvailabilityBroadcast

def encode (message : ServiceAvailabilityBroadcast) : List UInt8 :=
  Alpha.encode message.filler4
    ++ (NrbcHeaderComp.encode message.nrbcHeaderComp
    ++ (encodeUIntLE 4 message.matchingEngineTradeDate
    ++ (encodeUIntLE 4 message.tradeManagerTradeDate
    ++ (encodeUIntLE 4 message.applSeqTradeDate
    ++ (encodeUIntLE 2 message.partitionId
    ++ (encodeUInt 1 message.matchingEngineStatus
    ++ (encodeUInt 1 message.tradeManagerStatus
    ++ (encodeUInt 1 message.applSeqStatus
    ++ (Alpha.encode message.pad7)))))))))

def decode (bytes : List UInt8) : Option (ServiceAvailabilityBroadcast × List UInt8) := do
  let (filler4, bytes) ← Alpha.decode 2 bytes
  let (nrbcHeaderComp, bytes) ← NrbcHeaderComp.decode bytes
  let (matchingEngineTradeDate, bytes) ← decodeUIntLE 4 bytes
  let (tradeManagerTradeDate, bytes) ← decodeUIntLE 4 bytes
  let (applSeqTradeDate, bytes) ← decodeUIntLE 4 bytes
  let (partitionId, bytes) ← decodeUIntLE 2 bytes
  let (matchingEngineStatus, bytes) ← decodeUInt 1 bytes
  let (tradeManagerStatus, bytes) ← decodeUInt 1 bytes
  let (applSeqStatus, bytes) ← decodeUInt 1 bytes
  let (pad7, bytes) ← Alpha.decode 7 bytes
  pure ({ filler4, nrbcHeaderComp, matchingEngineTradeDate, tradeManagerTradeDate, applSeqTradeDate, partitionId, matchingEngineStatus, tradeManagerStatus, applSeqStatus, pad7 }, bytes)

@[simp] theorem encode_length (message : ServiceAvailabilityBroadcast) : (encode message).length = 42 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, NrbcHeaderComp.encode_length, encodeUIntLE_length, encodeUInt_length]

theorem encode_length_pos (message : ServiceAvailabilityBroadcast) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : ServiceAvailabilityBroadcast) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, NrbcHeaderComp.decode_encode, some_bind]
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
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : ServiceAvailabilityBroadcast) : decode (encode message) = some (message, []) :=
  List.append_nil (encode message) ▸ decode_encode message []

end ServiceAvailabilityBroadcast

/-- Session Password Change Response: 26 bytes -/
structure SessionPasswordChangeResponse where
  filler4 : Alpha 2
  responseHeaderComp : ResponseHeaderComp
  deriving DecidableEq, Repr

namespace SessionPasswordChangeResponse

def encode (message : SessionPasswordChangeResponse) : List UInt8 :=
  Alpha.encode message.filler4
    ++ (ResponseHeaderComp.encode message.responseHeaderComp)

def decode (bytes : List UInt8) : Option (SessionPasswordChangeResponse × List UInt8) := do
  let (filler4, bytes) ← Alpha.decode 2 bytes
  let (responseHeaderComp, bytes) ← ResponseHeaderComp.decode bytes
  pure ({ filler4, responseHeaderComp }, bytes)

@[simp] theorem encode_length (message : SessionPasswordChangeResponse) : (encode message).length = 26 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, ResponseHeaderComp.encode_length]

theorem encode_length_pos (message : SessionPasswordChangeResponse) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SessionPasswordChangeResponse) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [ResponseHeaderComp.decode_encode, some_bind]
  rfl

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : SessionPasswordChangeResponse) : decode (encode message) = some (message, []) :=
  List.append_nil (encode message) ▸ decode_encode message []

end SessionPasswordChangeResponse

/-- Session Registration Response -/
structure SessionRegistrationResponse where
  filler4 : Alpha 2
  responseHeaderComp : ResponseHeaderComp
  status : Status
  pad1 : Alpha 1
  pad4 : Alpha 4
  varText : Bounded 2 UInt8
  alignmentPadding : Capped 7
  deriving DecidableEq, Repr

namespace SessionRegistrationResponse

def encode (message : SessionRegistrationResponse) : List UInt8 :=
  Alpha.encode message.filler4
    ++ (ResponseHeaderComp.encode message.responseHeaderComp
    ++ (Status.encode message.status
    ++ (Alpha.encode message.pad1
    ++ (encodeUIntLE 2 (BitVec.ofNat (8 * 2) message.varText.val.length)
    ++ (Alpha.encode message.pad4
    ++ (encodeMany Byte.encode message.varText.val
    ++ (message.alignmentPadding.val)))))))

def decode (bytes : List UInt8) : Option SessionRegistrationResponse := do
  let (filler4, bytes) ← Alpha.decode 2 bytes
  let (responseHeaderComp, bytes) ← ResponseHeaderComp.decode bytes
  let (status, bytes) ← Status.decode bytes
  let (pad1, bytes) ← Alpha.decode 1 bytes
  let (varTextLen, bytes) ← decodeUIntLE 2 bytes
  let (pad4, bytes) ← Alpha.decode 4 bytes
  let (varText_, bytes) ← decodeMany Byte.decode varTextLen.toNat bytes
  let alignmentPadding_ := bytes
  if fits_varText : varText_.length < 256 ^ 2 then
    if fits_alignmentPadding : alignmentPadding_.length ≤ 7 then
      pure { filler4, responseHeaderComp, status, pad1, pad4, varText := ⟨varText_, fits_varText⟩, alignmentPadding := ⟨alignmentPadding_, fits_alignmentPadding⟩ }
    else none
  else none

theorem encode_length_pos (message : SessionRegistrationResponse) : (encode message).length > 0 := by
  unfold encode
  simp only [Alpha.encode_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : SessionRegistrationResponse) : (encode message).length ≤ 65576 := by
  have bound_varText := message.varText.length_lt
  have bound_alignmentPadding := message.alignmentPadding.length_le
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, Alpha.encode_length, ResponseHeaderComp.encode_length, Status.encode_length, encodeUIntLE_length, encodeMany_length_const Byte.encode 1 Byte.encode_length]
  omega

theorem decode_encode (message : SessionRegistrationResponse) : decode (encode message) = some message := by
  unfold decode encode
  rw [Alpha.decode_encode, some_bind]
  dsimp only
  rw [ResponseHeaderComp.decode_encode, some_bind]
  dsimp only
  rw [Status.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  dsimp only
  rw [decodeMany_bounded 2 Byte.encode Byte.decode Byte.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.varText.length_lt, dite_eq_left message.alignmentPadding.length_le]
  rfl

end SessionRegistrationResponse

/-- Subscribe Response: 34 bytes -/
structure SubscribeResponse where
  filler4 : Alpha 2
  responseHeaderComp : ResponseHeaderComp
  applSubId : BitVec 32
  pad4 : Alpha 4
  deriving DecidableEq, Repr

namespace SubscribeResponse

def encode (message : SubscribeResponse) : List UInt8 :=
  Alpha.encode message.filler4
    ++ (ResponseHeaderComp.encode message.responseHeaderComp
    ++ (encodeUIntLE 4 message.applSubId
    ++ (Alpha.encode message.pad4)))

def decode (bytes : List UInt8) : Option (SubscribeResponse × List UInt8) := do
  let (filler4, bytes) ← Alpha.decode 2 bytes
  let (responseHeaderComp, bytes) ← ResponseHeaderComp.decode bytes
  let (applSubId, bytes) ← decodeUIntLE 4 bytes
  let (pad4, bytes) ← Alpha.decode 4 bytes
  pure ({ filler4, responseHeaderComp, applSubId, pad4 }, bytes)

@[simp] theorem encode_length (message : SubscribeResponse) : (encode message).length = 34 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, ResponseHeaderComp.encode_length, encodeUIntLE_length]

theorem encode_length_pos (message : SubscribeResponse) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SubscribeResponse) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, ResponseHeaderComp.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : SubscribeResponse) : decode (encode message) = some (message, []) :=
  List.append_nil (encode message) ▸ decode_encode message []

end SubscribeResponse

/-- Tm Trading Session Status Broadcast: 42 bytes -/
structure TmTradingSessionStatusBroadcast where
  filler4 : Alpha 2
  rbcHeaderComp : RbcHeaderComp
  tradSesEvent : BitVec 8
  pad7 : Alpha 7
  deriving DecidableEq, Repr

namespace TmTradingSessionStatusBroadcast

def encode (message : TmTradingSessionStatusBroadcast) : List UInt8 :=
  Alpha.encode message.filler4
    ++ (RbcHeaderComp.encode message.rbcHeaderComp
    ++ (encodeUInt 1 message.tradSesEvent
    ++ (Alpha.encode message.pad7)))

def decode (bytes : List UInt8) : Option (TmTradingSessionStatusBroadcast × List UInt8) := do
  let (filler4, bytes) ← Alpha.decode 2 bytes
  let (rbcHeaderComp, bytes) ← RbcHeaderComp.decode bytes
  let (tradSesEvent, bytes) ← decodeUInt 1 bytes
  let (pad7, bytes) ← Alpha.decode 7 bytes
  pure ({ filler4, rbcHeaderComp, tradSesEvent, pad7 }, bytes)

@[simp] theorem encode_length (message : TmTradingSessionStatusBroadcast) : (encode message).length = 42 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, RbcHeaderComp.encode_length, encodeUInt_length]

theorem encode_length_pos (message : TmTradingSessionStatusBroadcast) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : TmTradingSessionStatusBroadcast) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, RbcHeaderComp.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : TmTradingSessionStatusBroadcast) : decode (encode message) = some (message, []) :=
  List.append_nil (encode message) ▸ decode_encode message []

end TmTradingSessionStatusBroadcast

/-- Throttle Update Notification: 26 bytes -/
structure ThrottleUpdateNotification where
  filler4 : Alpha 2
  notifHeaderComp : NotifHeaderComp
  throttleTimeInterval : BitVec 64
  throttleNoMsgs : BitVec 32
  throttleDisconnectLimit : BitVec 32
  deriving DecidableEq, Repr

namespace ThrottleUpdateNotification

def encode (message : ThrottleUpdateNotification) : List UInt8 :=
  Alpha.encode message.filler4
    ++ (NotifHeaderComp.encode message.notifHeaderComp
    ++ (encodeUIntLE 8 message.throttleTimeInterval
    ++ (encodeUIntLE 4 message.throttleNoMsgs
    ++ (encodeUIntLE 4 message.throttleDisconnectLimit))))

def decode (bytes : List UInt8) : Option (ThrottleUpdateNotification × List UInt8) := do
  let (filler4, bytes) ← Alpha.decode 2 bytes
  let (notifHeaderComp, bytes) ← NotifHeaderComp.decode bytes
  let (throttleTimeInterval, bytes) ← decodeUIntLE 8 bytes
  let (throttleNoMsgs, bytes) ← decodeUIntLE 4 bytes
  let (throttleDisconnectLimit, bytes) ← decodeUIntLE 4 bytes
  pure ({ filler4, notifHeaderComp, throttleTimeInterval, throttleNoMsgs, throttleDisconnectLimit }, bytes)

@[simp] theorem encode_length (message : ThrottleUpdateNotification) : (encode message).length = 26 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, NotifHeaderComp.encode_length, encodeUIntLE_length]

theorem encode_length_pos (message : ThrottleUpdateNotification) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : ThrottleUpdateNotification) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, NotifHeaderComp.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : ThrottleUpdateNotification) : decode (encode message) = some (message, []) :=
  List.append_nil (encode message) ▸ decode_encode message []

end ThrottleUpdateNotification

/-- Trade Broadcast: 346 bytes -/
structure TradeBroadcast where
  filler4 : Alpha 2
  rbcHeaderComp : RbcHeaderComp
  securityId : BitVec 64
  relatedSecurityId : BitVec 64
  price : BitVec 64
  lastPx : BitVec 64
  sideLastPx : BitVec 64
  clearingTradePrice : BitVec 64
  yield : BitVec 64
  underlyingDirtyPrice : BitVec 64
  transactTime : BitVec 64
  orderId : BitVec 64
  senderLocationId : BitVec 64
  clOrdId : BitVec 64
  activityTime : BitVec 64
  filler1 : Alpha 8
  filler2 : Alpha 4
  messageTag : BitVec 32
  tradeId : BitVec 32
  origTradeId : BitVec 32
  rootPartyIdExecutingUnit : BitVec 32
  rootPartyIdSessionId : BitVec 32
  rootPartyIdExecutingTrader : BitVec 32
  rootPartyIdClearingUnit : BitVec 32
  cumQty : BitVec 32
  leavesQty : BitVec 32
  marketSegmentId : BitVec 32
  relatedSymbol : BitVec 32
  lastQty : BitVec 32
  sideLastQty : BitVec 32
  clearingTradeQty : BitVec 32
  sideTradeId : BitVec 32
  matchDate : BitVec 32
  trdMatchId : BitVec 32
  strategyLinkId : BitVec 32
  totNumTradeReports : BitVec 32
  filler4v2 : Alpha 2
  multiLegReportingType : BitVec 8
  tradeReportType : BitVec 8
  transferReason : BitVec 8
  rolloverFlag : BitVec 8
  rootPartyIdBeneficiary : Alpha 9
  rootPartyIdTakeUpTradingFirm : Alpha 5
  rootPartyIdOrderOriginationFirm : Alpha 7
  accountType : BitVec 8
  matchType : BitVec 8
  matchSubType : BitVec 8
  side : BitVec 8
  aggressorIndicator : BitVec 8
  tradingCapacity : BitVec 8
  account : Alpha 2
  positionEffect : Alpha 1
  custOrderHandlingInst : Alpha 1
  algoId : Alpha 16
  clientCode : Alpha 12
  cpCode : Alpha 12
  freeText3 : Alpha 12
  orderCategory : OrderCategory
  ordType : BitVec 8
  relatedProductComplex : BitVec 8
  orderSide : BitVec 8
  rootPartyClearingOrganization : Alpha 4
  rootPartyExecutingFirm : Alpha 5
  rootPartyExecutingTrader : Alpha 6
  rootPartyClearingFirm : Alpha 5
  pad7 : Alpha 7
  deriving DecidableEq, Repr

namespace TradeBroadcast

def encode (message : TradeBroadcast) : List UInt8 :=
  Alpha.encode message.filler4
    ++ (RbcHeaderComp.encode message.rbcHeaderComp
    ++ (encodeUIntLE 8 message.securityId
    ++ (encodeUIntLE 8 message.relatedSecurityId
    ++ (encodeUIntLE 8 message.price
    ++ (encodeUIntLE 8 message.lastPx
    ++ (encodeUIntLE 8 message.sideLastPx
    ++ (encodeUIntLE 8 message.clearingTradePrice
    ++ (encodeUIntLE 8 message.yield
    ++ (encodeUIntLE 8 message.underlyingDirtyPrice
    ++ (encodeUIntLE 8 message.transactTime
    ++ (encodeUIntLE 8 message.orderId
    ++ (encodeUIntLE 8 message.senderLocationId
    ++ (encodeUIntLE 8 message.clOrdId
    ++ (encodeUIntLE 8 message.activityTime
    ++ (Alpha.encode message.filler1
    ++ (Alpha.encode message.filler2
    ++ (encodeUIntLE 4 message.messageTag
    ++ (encodeUIntLE 4 message.tradeId
    ++ (encodeUIntLE 4 message.origTradeId
    ++ (encodeUIntLE 4 message.rootPartyIdExecutingUnit
    ++ (encodeUIntLE 4 message.rootPartyIdSessionId
    ++ (encodeUIntLE 4 message.rootPartyIdExecutingTrader
    ++ (encodeUIntLE 4 message.rootPartyIdClearingUnit
    ++ (encodeUIntLE 4 message.cumQty
    ++ (encodeUIntLE 4 message.leavesQty
    ++ (encodeUIntLE 4 message.marketSegmentId
    ++ (encodeUIntLE 4 message.relatedSymbol
    ++ (encodeUIntLE 4 message.lastQty
    ++ (encodeUIntLE 4 message.sideLastQty
    ++ (encodeUIntLE 4 message.clearingTradeQty
    ++ (encodeUIntLE 4 message.sideTradeId
    ++ (encodeUIntLE 4 message.matchDate
    ++ (encodeUIntLE 4 message.trdMatchId
    ++ (encodeUIntLE 4 message.strategyLinkId
    ++ (encodeUIntLE 4 message.totNumTradeReports
    ++ (Alpha.encode message.filler4v2
    ++ (encodeUInt 1 message.multiLegReportingType
    ++ (encodeUInt 1 message.tradeReportType
    ++ (encodeUInt 1 message.transferReason
    ++ (encodeUInt 1 message.rolloverFlag
    ++ (Alpha.encode message.rootPartyIdBeneficiary
    ++ (Alpha.encode message.rootPartyIdTakeUpTradingFirm
    ++ (Alpha.encode message.rootPartyIdOrderOriginationFirm
    ++ (encodeUInt 1 message.accountType
    ++ (encodeUInt 1 message.matchType
    ++ (encodeUInt 1 message.matchSubType
    ++ (encodeUInt 1 message.side
    ++ (encodeUInt 1 message.aggressorIndicator
    ++ (encodeUInt 1 message.tradingCapacity
    ++ (Alpha.encode message.account
    ++ (Alpha.encode message.positionEffect
    ++ (Alpha.encode message.custOrderHandlingInst
    ++ (Alpha.encode message.algoId
    ++ (Alpha.encode message.clientCode
    ++ (Alpha.encode message.cpCode
    ++ (Alpha.encode message.freeText3
    ++ (OrderCategory.encode message.orderCategory
    ++ (encodeUInt 1 message.ordType
    ++ (encodeUInt 1 message.relatedProductComplex
    ++ (encodeUInt 1 message.orderSide
    ++ (Alpha.encode message.rootPartyClearingOrganization
    ++ (Alpha.encode message.rootPartyExecutingFirm
    ++ (Alpha.encode message.rootPartyExecutingTrader
    ++ (Alpha.encode message.rootPartyClearingFirm
    ++ (Alpha.encode message.pad7)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

-- a long run of fields nests deeper than the elaborator's default limit
set_option maxRecDepth 4096 in
def decode (bytes : List UInt8) : Option (TradeBroadcast × List UInt8) := do
  let (filler4, bytes) ← Alpha.decode 2 bytes
  let (rbcHeaderComp, bytes) ← RbcHeaderComp.decode bytes
  let (securityId, bytes) ← decodeUIntLE 8 bytes
  let (relatedSecurityId, bytes) ← decodeUIntLE 8 bytes
  let (price, bytes) ← decodeUIntLE 8 bytes
  let (lastPx, bytes) ← decodeUIntLE 8 bytes
  let (sideLastPx, bytes) ← decodeUIntLE 8 bytes
  let (clearingTradePrice, bytes) ← decodeUIntLE 8 bytes
  let (yield, bytes) ← decodeUIntLE 8 bytes
  let (underlyingDirtyPrice, bytes) ← decodeUIntLE 8 bytes
  let (transactTime, bytes) ← decodeUIntLE 8 bytes
  let (orderId, bytes) ← decodeUIntLE 8 bytes
  let (senderLocationId, bytes) ← decodeUIntLE 8 bytes
  let (clOrdId, bytes) ← decodeUIntLE 8 bytes
  let (activityTime, bytes) ← decodeUIntLE 8 bytes
  let (filler1, bytes) ← Alpha.decode 8 bytes
  let (filler2, bytes) ← Alpha.decode 4 bytes
  let (messageTag, bytes) ← decodeUIntLE 4 bytes
  let (tradeId, bytes) ← decodeUIntLE 4 bytes
  let (origTradeId, bytes) ← decodeUIntLE 4 bytes
  let (rootPartyIdExecutingUnit, bytes) ← decodeUIntLE 4 bytes
  let (rootPartyIdSessionId, bytes) ← decodeUIntLE 4 bytes
  let (rootPartyIdExecutingTrader, bytes) ← decodeUIntLE 4 bytes
  let (rootPartyIdClearingUnit, bytes) ← decodeUIntLE 4 bytes
  let (cumQty, bytes) ← decodeUIntLE 4 bytes
  let (leavesQty, bytes) ← decodeUIntLE 4 bytes
  let (marketSegmentId, bytes) ← decodeUIntLE 4 bytes
  let (relatedSymbol, bytes) ← decodeUIntLE 4 bytes
  let (lastQty, bytes) ← decodeUIntLE 4 bytes
  let (sideLastQty, bytes) ← decodeUIntLE 4 bytes
  let (clearingTradeQty, bytes) ← decodeUIntLE 4 bytes
  let (sideTradeId, bytes) ← decodeUIntLE 4 bytes
  let (matchDate, bytes) ← decodeUIntLE 4 bytes
  let (trdMatchId, bytes) ← decodeUIntLE 4 bytes
  let (strategyLinkId, bytes) ← decodeUIntLE 4 bytes
  let (totNumTradeReports, bytes) ← decodeUIntLE 4 bytes
  let (filler4v2, bytes) ← Alpha.decode 2 bytes
  let (multiLegReportingType, bytes) ← decodeUInt 1 bytes
  let (tradeReportType, bytes) ← decodeUInt 1 bytes
  let (transferReason, bytes) ← decodeUInt 1 bytes
  let (rolloverFlag, bytes) ← decodeUInt 1 bytes
  let (rootPartyIdBeneficiary, bytes) ← Alpha.decode 9 bytes
  let (rootPartyIdTakeUpTradingFirm, bytes) ← Alpha.decode 5 bytes
  let (rootPartyIdOrderOriginationFirm, bytes) ← Alpha.decode 7 bytes
  let (accountType, bytes) ← decodeUInt 1 bytes
  let (matchType, bytes) ← decodeUInt 1 bytes
  let (matchSubType, bytes) ← decodeUInt 1 bytes
  let (side, bytes) ← decodeUInt 1 bytes
  let (aggressorIndicator, bytes) ← decodeUInt 1 bytes
  let (tradingCapacity, bytes) ← decodeUInt 1 bytes
  let (account, bytes) ← Alpha.decode 2 bytes
  let (positionEffect, bytes) ← Alpha.decode 1 bytes
  let (custOrderHandlingInst, bytes) ← Alpha.decode 1 bytes
  let (algoId, bytes) ← Alpha.decode 16 bytes
  let (clientCode, bytes) ← Alpha.decode 12 bytes
  let (cpCode, bytes) ← Alpha.decode 12 bytes
  let (freeText3, bytes) ← Alpha.decode 12 bytes
  let (orderCategory, bytes) ← OrderCategory.decode bytes
  let (ordType, bytes) ← decodeUInt 1 bytes
  let (relatedProductComplex, bytes) ← decodeUInt 1 bytes
  let (orderSide, bytes) ← decodeUInt 1 bytes
  let (rootPartyClearingOrganization, bytes) ← Alpha.decode 4 bytes
  let (rootPartyExecutingFirm, bytes) ← Alpha.decode 5 bytes
  let (rootPartyExecutingTrader, bytes) ← Alpha.decode 6 bytes
  let (rootPartyClearingFirm, bytes) ← Alpha.decode 5 bytes
  let (pad7, bytes) ← Alpha.decode 7 bytes
  pure ({ filler4, rbcHeaderComp, securityId, relatedSecurityId, price, lastPx, sideLastPx, clearingTradePrice, yield, underlyingDirtyPrice, transactTime, orderId, senderLocationId, clOrdId, activityTime, filler1, filler2, messageTag, tradeId, origTradeId, rootPartyIdExecutingUnit, rootPartyIdSessionId, rootPartyIdExecutingTrader, rootPartyIdClearingUnit, cumQty, leavesQty, marketSegmentId, relatedSymbol, lastQty, sideLastQty, clearingTradeQty, sideTradeId, matchDate, trdMatchId, strategyLinkId, totNumTradeReports, filler4v2, multiLegReportingType, tradeReportType, transferReason, rolloverFlag, rootPartyIdBeneficiary, rootPartyIdTakeUpTradingFirm, rootPartyIdOrderOriginationFirm, accountType, matchType, matchSubType, side, aggressorIndicator, tradingCapacity, account, positionEffect, custOrderHandlingInst, algoId, clientCode, cpCode, freeText3, orderCategory, ordType, relatedProductComplex, orderSide, rootPartyClearingOrganization, rootPartyExecutingFirm, rootPartyExecutingTrader, rootPartyClearingFirm, pad7 }, bytes)

@[simp] theorem encode_length (message : TradeBroadcast) : (encode message).length = 346 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, RbcHeaderComp.encode_length, encodeUIntLE_length, encodeUInt_length, OrderCategory.encode_length]

theorem encode_length_pos (message : TradeBroadcast) : (encode message).length > 0 := by
  rw [encode_length]
  decide

set_option maxRecDepth 4096 in
@[simp] theorem decode_encode (message : TradeBroadcast) (rest : List UInt8) :
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
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
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
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, OrderCategory.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
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
  rw [Alpha.decode_encode, some_bind]
  rfl

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : TradeBroadcast) : decode (encode message) = some (message, []) :=
  List.append_nil (encode message) ▸ decode_encode message []

end TradeBroadcast

/-- Trade Enhancement Broadcast: 122 bytes -/
structure TradeEnhancementBroadcast where
  filler4 : Alpha 2
  rbcHeaderComp : RbcHeaderComp
  securityId : BitVec 64
  clearingTradePrice : BitVec 64
  transactTime : BitVec 64
  orderId : BitVec 64
  tradeId : BitVec 32
  rootPartyIdSessionId : BitVec 32
  sideTradeId : BitVec 32
  marketSegmentId : BitVec 32
  matchDate : BitVec 32
  clearingTradeQty : BitVec 32
  accountType : BitVec 8
  side : BitVec 8
  autoAcceptIndicator : AutoAcceptIndicator
  cpCode : Alpha 12
  clientCode : Alpha 12
  pad5 : Alpha 5
  deriving DecidableEq, Repr

namespace TradeEnhancementBroadcast

def encode (message : TradeEnhancementBroadcast) : List UInt8 :=
  Alpha.encode message.filler4
    ++ (RbcHeaderComp.encode message.rbcHeaderComp
    ++ (encodeUIntLE 8 message.securityId
    ++ (encodeUIntLE 8 message.clearingTradePrice
    ++ (encodeUIntLE 8 message.transactTime
    ++ (encodeUIntLE 8 message.orderId
    ++ (encodeUIntLE 4 message.tradeId
    ++ (encodeUIntLE 4 message.rootPartyIdSessionId
    ++ (encodeUIntLE 4 message.sideTradeId
    ++ (encodeUIntLE 4 message.marketSegmentId
    ++ (encodeUIntLE 4 message.matchDate
    ++ (encodeUIntLE 4 message.clearingTradeQty
    ++ (encodeUInt 1 message.accountType
    ++ (encodeUInt 1 message.side
    ++ (AutoAcceptIndicator.encode message.autoAcceptIndicator
    ++ (Alpha.encode message.cpCode
    ++ (Alpha.encode message.clientCode
    ++ (Alpha.encode message.pad5)))))))))))))))))

def decode (bytes : List UInt8) : Option (TradeEnhancementBroadcast × List UInt8) := do
  let (filler4, bytes) ← Alpha.decode 2 bytes
  let (rbcHeaderComp, bytes) ← RbcHeaderComp.decode bytes
  let (securityId, bytes) ← decodeUIntLE 8 bytes
  let (clearingTradePrice, bytes) ← decodeUIntLE 8 bytes
  let (transactTime, bytes) ← decodeUIntLE 8 bytes
  let (orderId, bytes) ← decodeUIntLE 8 bytes
  let (tradeId, bytes) ← decodeUIntLE 4 bytes
  let (rootPartyIdSessionId, bytes) ← decodeUIntLE 4 bytes
  let (sideTradeId, bytes) ← decodeUIntLE 4 bytes
  let (marketSegmentId, bytes) ← decodeUIntLE 4 bytes
  let (matchDate, bytes) ← decodeUIntLE 4 bytes
  let (clearingTradeQty, bytes) ← decodeUIntLE 4 bytes
  let (accountType, bytes) ← decodeUInt 1 bytes
  let (side, bytes) ← decodeUInt 1 bytes
  let (autoAcceptIndicator, bytes) ← AutoAcceptIndicator.decode bytes
  let (cpCode, bytes) ← Alpha.decode 12 bytes
  let (clientCode, bytes) ← Alpha.decode 12 bytes
  let (pad5, bytes) ← Alpha.decode 5 bytes
  pure ({ filler4, rbcHeaderComp, securityId, clearingTradePrice, transactTime, orderId, tradeId, rootPartyIdSessionId, sideTradeId, marketSegmentId, matchDate, clearingTradeQty, accountType, side, autoAcceptIndicator, cpCode, clientCode, pad5 }, bytes)

@[simp] theorem encode_length (message : TradeEnhancementBroadcast) : (encode message).length = 122 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, RbcHeaderComp.encode_length, encodeUIntLE_length, encodeUInt_length, AutoAcceptIndicator.encode_length]

theorem encode_length_pos (message : TradeEnhancementBroadcast) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : TradeEnhancementBroadcast) (rest : List UInt8) :
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
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, AutoAcceptIndicator.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : TradeEnhancementBroadcast) : decode (encode message) = some (message, []) :=
  List.append_nil (encode message) ▸ decode_encode message []

end TradeEnhancementBroadcast

/-- Trading Session Status Broadcast: 82 bytes -/
structure TradingSessionStatusBroadcast where
  filler4 : Alpha 2
  rbcHeaderMeComp : RbcHeaderMeComp
  marketSegmentId : BitVec 32
  tradeDate : BitVec 32
  tradSesEvent : BitVec 8
  refApplLastMsgId : Alpha 16
  pad7 : Alpha 7
  deriving DecidableEq, Repr

namespace TradingSessionStatusBroadcast

def encode (message : TradingSessionStatusBroadcast) : List UInt8 :=
  Alpha.encode message.filler4
    ++ (RbcHeaderMeComp.encode message.rbcHeaderMeComp
    ++ (encodeUIntLE 4 message.marketSegmentId
    ++ (encodeUIntLE 4 message.tradeDate
    ++ (encodeUInt 1 message.tradSesEvent
    ++ (Alpha.encode message.refApplLastMsgId
    ++ (Alpha.encode message.pad7))))))

def decode (bytes : List UInt8) : Option (TradingSessionStatusBroadcast × List UInt8) := do
  let (filler4, bytes) ← Alpha.decode 2 bytes
  let (rbcHeaderMeComp, bytes) ← RbcHeaderMeComp.decode bytes
  let (marketSegmentId, bytes) ← decodeUIntLE 4 bytes
  let (tradeDate, bytes) ← decodeUIntLE 4 bytes
  let (tradSesEvent, bytes) ← decodeUInt 1 bytes
  let (refApplLastMsgId, bytes) ← Alpha.decode 16 bytes
  let (pad7, bytes) ← Alpha.decode 7 bytes
  pure ({ filler4, rbcHeaderMeComp, marketSegmentId, tradeDate, tradSesEvent, refApplLastMsgId, pad7 }, bytes)

@[simp] theorem encode_length (message : TradingSessionStatusBroadcast) : (encode message).length = 82 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, RbcHeaderMeComp.encode_length, encodeUIntLE_length, encodeUInt_length]

theorem encode_length_pos (message : TradingSessionStatusBroadcast) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : TradingSessionStatusBroadcast) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, RbcHeaderMeComp.decode_encode, some_bind]
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

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : TradingSessionStatusBroadcast) : decode (encode message) = some (message, []) :=
  List.append_nil (encode message) ▸ decode_encode message []

end TradingSessionStatusBroadcast

/-- Unsubscribe Response: 26 bytes -/
structure UnsubscribeResponse where
  filler4 : Alpha 2
  responseHeaderComp : ResponseHeaderComp
  deriving DecidableEq, Repr

namespace UnsubscribeResponse

def encode (message : UnsubscribeResponse) : List UInt8 :=
  Alpha.encode message.filler4
    ++ (ResponseHeaderComp.encode message.responseHeaderComp)

def decode (bytes : List UInt8) : Option (UnsubscribeResponse × List UInt8) := do
  let (filler4, bytes) ← Alpha.decode 2 bytes
  let (responseHeaderComp, bytes) ← ResponseHeaderComp.decode bytes
  pure ({ filler4, responseHeaderComp }, bytes)

@[simp] theorem encode_length (message : UnsubscribeResponse) : (encode message).length = 26 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, ResponseHeaderComp.encode_length]

theorem encode_length_pos (message : UnsubscribeResponse) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : UnsubscribeResponse) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [ResponseHeaderComp.decode_encode, some_bind]
  rfl

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : UnsubscribeResponse) : decode (encode message) = some (message, []) :=
  List.append_nil (encode message) ▸ decode_encode message []

end UnsubscribeResponse

/-- User Login Response: 42 bytes -/
structure UserLoginResponse where
  filler4 : Alpha 2
  responseHeaderComp : ResponseHeaderComp
  lastLoginTime : BitVec 64
  daysLeftForPasswdExpiry : BitVec 8
  graceLoginsLeft : BitVec 8
  pad6 : Alpha 6
  deriving DecidableEq, Repr

namespace UserLoginResponse

def encode (message : UserLoginResponse) : List UInt8 :=
  Alpha.encode message.filler4
    ++ (ResponseHeaderComp.encode message.responseHeaderComp
    ++ (encodeUIntLE 8 message.lastLoginTime
    ++ (encodeUInt 1 message.daysLeftForPasswdExpiry
    ++ (encodeUInt 1 message.graceLoginsLeft
    ++ (Alpha.encode message.pad6)))))

def decode (bytes : List UInt8) : Option (UserLoginResponse × List UInt8) := do
  let (filler4, bytes) ← Alpha.decode 2 bytes
  let (responseHeaderComp, bytes) ← ResponseHeaderComp.decode bytes
  let (lastLoginTime, bytes) ← decodeUIntLE 8 bytes
  let (daysLeftForPasswdExpiry, bytes) ← decodeUInt 1 bytes
  let (graceLoginsLeft, bytes) ← decodeUInt 1 bytes
  let (pad6, bytes) ← Alpha.decode 6 bytes
  pure ({ filler4, responseHeaderComp, lastLoginTime, daysLeftForPasswdExpiry, graceLoginsLeft, pad6 }, bytes)

@[simp] theorem encode_length (message : UserLoginResponse) : (encode message).length = 42 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, ResponseHeaderComp.encode_length, encodeUIntLE_length, encodeUInt_length]

theorem encode_length_pos (message : UserLoginResponse) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : UserLoginResponse) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, ResponseHeaderComp.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : UserLoginResponse) : decode (encode message) = some (message, []) :=
  List.append_nil (encode message) ▸ decode_encode message []

end UserLoginResponse

/-- User Logout Response: 26 bytes -/
structure UserLogoutResponse where
  filler4 : Alpha 2
  responseHeaderComp : ResponseHeaderComp
  deriving DecidableEq, Repr

namespace UserLogoutResponse

def encode (message : UserLogoutResponse) : List UInt8 :=
  Alpha.encode message.filler4
    ++ (ResponseHeaderComp.encode message.responseHeaderComp)

def decode (bytes : List UInt8) : Option (UserLogoutResponse × List UInt8) := do
  let (filler4, bytes) ← Alpha.decode 2 bytes
  let (responseHeaderComp, bytes) ← ResponseHeaderComp.decode bytes
  pure ({ filler4, responseHeaderComp }, bytes)

@[simp] theorem encode_length (message : UserLogoutResponse) : (encode message).length = 26 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, ResponseHeaderComp.encode_length]

theorem encode_length_pos (message : UserLogoutResponse) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : UserLogoutResponse) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [ResponseHeaderComp.decode_encode, some_bind]
  rfl

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : UserLogoutResponse) : decode (encode message) = some (message, []) :=
  List.append_nil (encode message) ▸ decode_encode message []

end UserLogoutResponse

/-- User Password Change Response: 26 bytes -/
structure UserPasswordChangeResponse where
  filler4 : Alpha 2
  responseHeaderComp : ResponseHeaderComp
  deriving DecidableEq, Repr

namespace UserPasswordChangeResponse

def encode (message : UserPasswordChangeResponse) : List UInt8 :=
  Alpha.encode message.filler4
    ++ (ResponseHeaderComp.encode message.responseHeaderComp)

def decode (bytes : List UInt8) : Option (UserPasswordChangeResponse × List UInt8) := do
  let (filler4, bytes) ← Alpha.decode 2 bytes
  let (responseHeaderComp, bytes) ← ResponseHeaderComp.decode bytes
  pure ({ filler4, responseHeaderComp }, bytes)

@[simp] theorem encode_length (message : UserPasswordChangeResponse) : (encode message).length = 26 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, ResponseHeaderComp.encode_length]

theorem encode_length_pos (message : UserPasswordChangeResponse) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : UserPasswordChangeResponse) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [ResponseHeaderComp.decode_encode, some_bind]
  rfl

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : UserPasswordChangeResponse) : decode (encode message) = some (message, []) :=
  List.append_nil (encode message) ▸ decode_encode message []

end UserPasswordChangeResponse

/-- Any Server Payload, selected by Template Id -/
inductive ServerPayload where
  | broadcastErrorNotification (message : BroadcastErrorNotification) -- 10032
  | debtInquiryResponse (message : DebtInquiryResponse) -- 10391
  | deleteAllOrderBroadcast (message : DeleteAllOrderBroadcast) -- 10122
  | deleteAllOrderNrResponse (message : DeleteAllOrderNrResponse) -- 10124
  | deleteAllOrderQuoteEventBroadcast (message : DeleteAllOrderQuoteEventBroadcast) -- 10308
  | deleteAllOrderResponse (message : DeleteAllOrderResponse) -- 10121
  | deleteAllQuoteBroadcast (message : DeleteAllQuoteBroadcast) -- 10410
  | deleteAllQuoteResponse (message : DeleteAllQuoteResponse) -- 10409
  | deleteOrderBroadcast (message : DeleteOrderBroadcast) -- 10112
  | deleteOrderNrResponse (message : DeleteOrderNrResponse) -- 10111
  | deleteOrderResponse (message : DeleteOrderResponse) -- 10110
  | forcedLogoutNotification (message : ForcedLogoutNotification) -- 10012
  | gatewayResponse (message : GatewayResponse) -- 10022
  | gwOrderAcknowledgement (message : GwOrderAcknowledgement) -- 10990
  | heartbeatNotification (message : HeartbeatNotification) -- 10023
  | inquireSessionListResponse (message : InquireSessionListResponse) -- 10036
  | logonResponse (message : LogonResponse) -- 10001
  | logoutResponse (message : LogoutResponse) -- 10003
  | massQuoteResponse (message : MassQuoteResponse) -- 10406
  | modifyOrderNrResponse (message : ModifyOrderNrResponse) -- 10108
  | modifyOrderResponse (message : ModifyOrderResponse) -- 10107
  | multiLegExecReportBroadcast (message : MultiLegExecReportBroadcast) -- 10994
  | multiLegExecResponse (message : MultiLegExecResponse) -- 10993
  | multiLegOrderReject (message : MultiLegOrderReject) -- 10992
  | newOrderNrResponse (message : NewOrderNrResponse) -- 10102
  | newOrderResponse (message : NewOrderResponse) -- 10101
  | newsBroadcast (message : NewsBroadcast) -- 10031
  | orderExecNotification (message : OrderExecNotification) -- 10104
  | orderExecReportBroadcast (message : OrderExecReportBroadcast) -- 10117
  | orderExecResponse (message : OrderExecResponse) -- 10103
  | quoteExecReportBroadcast (message : QuoteExecReportBroadcast) -- 10412
  | quoteExecutionReport (message : QuoteExecutionReport) -- 10407
  | reject (message : Reject) -- 10010
  | retransmitMeMessageResponse (message : RetransmitMeMessageResponse) -- 10027
  | retransmitResponse (message : RetransmitResponse) -- 10009
  | riskCollateralAlertAdminBroadcast (message : RiskCollateralAlertAdminBroadcast) -- 10048
  | riskCollateralAlertBroadcast (message : RiskCollateralAlertBroadcast) -- 10049
  | riskNotificationBroadcast (message : RiskNotificationBroadcast) -- 10033
  | serviceAvailabilityBroadcast (message : ServiceAvailabilityBroadcast) -- 10030
  | sessionPasswordChangeResponse (message : SessionPasswordChangeResponse) -- 10995
  | sessionRegistrationResponse (message : SessionRegistrationResponse) -- 10054
  | subscribeResponse (message : SubscribeResponse) -- 10005
  | tmTradingSessionStatusBroadcast (message : TmTradingSessionStatusBroadcast) -- 10501
  | throttleUpdateNotification (message : ThrottleUpdateNotification) -- 10028
  | tradeBroadcast (message : TradeBroadcast) -- 10500
  | tradeEnhancementBroadcast (message : TradeEnhancementBroadcast) -- 10989
  | tradingSessionStatusBroadcast (message : TradingSessionStatusBroadcast) -- 10307
  | unsubscribeResponse (message : UnsubscribeResponse) -- 10007
  | userLoginResponse (message : UserLoginResponse) -- 10019
  | userLogoutResponse (message : UserLogoutResponse) -- 10024
  | userPasswordChangeResponse (message : UserPasswordChangeResponse) -- 10043
  deriving DecidableEq, Repr

namespace ServerPayload

/-- The Template Id each message is sent under -/
def tag : ServerPayload → BitVec 16
  | .broadcastErrorNotification _ => 10032
  | .debtInquiryResponse _ => 10391
  | .deleteAllOrderBroadcast _ => 10122
  | .deleteAllOrderNrResponse _ => 10124
  | .deleteAllOrderQuoteEventBroadcast _ => 10308
  | .deleteAllOrderResponse _ => 10121
  | .deleteAllQuoteBroadcast _ => 10410
  | .deleteAllQuoteResponse _ => 10409
  | .deleteOrderBroadcast _ => 10112
  | .deleteOrderNrResponse _ => 10111
  | .deleteOrderResponse _ => 10110
  | .forcedLogoutNotification _ => 10012
  | .gatewayResponse _ => 10022
  | .gwOrderAcknowledgement _ => 10990
  | .heartbeatNotification _ => 10023
  | .inquireSessionListResponse _ => 10036
  | .logonResponse _ => 10001
  | .logoutResponse _ => 10003
  | .massQuoteResponse _ => 10406
  | .modifyOrderNrResponse _ => 10108
  | .modifyOrderResponse _ => 10107
  | .multiLegExecReportBroadcast _ => 10994
  | .multiLegExecResponse _ => 10993
  | .multiLegOrderReject _ => 10992
  | .newOrderNrResponse _ => 10102
  | .newOrderResponse _ => 10101
  | .newsBroadcast _ => 10031
  | .orderExecNotification _ => 10104
  | .orderExecReportBroadcast _ => 10117
  | .orderExecResponse _ => 10103
  | .quoteExecReportBroadcast _ => 10412
  | .quoteExecutionReport _ => 10407
  | .reject _ => 10010
  | .retransmitMeMessageResponse _ => 10027
  | .retransmitResponse _ => 10009
  | .riskCollateralAlertAdminBroadcast _ => 10048
  | .riskCollateralAlertBroadcast _ => 10049
  | .riskNotificationBroadcast _ => 10033
  | .serviceAvailabilityBroadcast _ => 10030
  | .sessionPasswordChangeResponse _ => 10995
  | .sessionRegistrationResponse _ => 10054
  | .subscribeResponse _ => 10005
  | .tmTradingSessionStatusBroadcast _ => 10501
  | .throttleUpdateNotification _ => 10028
  | .tradeBroadcast _ => 10500
  | .tradeEnhancementBroadcast _ => 10989
  | .tradingSessionStatusBroadcast _ => 10307
  | .unsubscribeResponse _ => 10007
  | .userLoginResponse _ => 10019
  | .userLogoutResponse _ => 10024
  | .userPasswordChangeResponse _ => 10043

def encode : ServerPayload → List UInt8
  | .broadcastErrorNotification message => BroadcastErrorNotification.encode message
  | .debtInquiryResponse message => DebtInquiryResponse.encode message
  | .deleteAllOrderBroadcast message => DeleteAllOrderBroadcast.encode message
  | .deleteAllOrderNrResponse message => DeleteAllOrderNrResponse.encode message
  | .deleteAllOrderQuoteEventBroadcast message => DeleteAllOrderQuoteEventBroadcast.encode message
  | .deleteAllOrderResponse message => DeleteAllOrderResponse.encode message
  | .deleteAllQuoteBroadcast message => DeleteAllQuoteBroadcast.encode message
  | .deleteAllQuoteResponse message => DeleteAllQuoteResponse.encode message
  | .deleteOrderBroadcast message => DeleteOrderBroadcast.encode message
  | .deleteOrderNrResponse message => DeleteOrderNrResponse.encode message
  | .deleteOrderResponse message => DeleteOrderResponse.encode message
  | .forcedLogoutNotification message => ForcedLogoutNotification.encode message
  | .gatewayResponse message => GatewayResponse.encode message
  | .gwOrderAcknowledgement message => GwOrderAcknowledgement.encode message
  | .heartbeatNotification message => HeartbeatNotification.encode message
  | .inquireSessionListResponse message => InquireSessionListResponse.encode message
  | .logonResponse message => LogonResponse.encode message
  | .logoutResponse message => LogoutResponse.encode message
  | .massQuoteResponse message => MassQuoteResponse.encode message
  | .modifyOrderNrResponse message => ModifyOrderNrResponse.encode message
  | .modifyOrderResponse message => ModifyOrderResponse.encode message
  | .multiLegExecReportBroadcast message => MultiLegExecReportBroadcast.encode message
  | .multiLegExecResponse message => MultiLegExecResponse.encode message
  | .multiLegOrderReject message => MultiLegOrderReject.encode message
  | .newOrderNrResponse message => NewOrderNrResponse.encode message
  | .newOrderResponse message => NewOrderResponse.encode message
  | .newsBroadcast message => NewsBroadcast.encode message
  | .orderExecNotification message => OrderExecNotification.encode message
  | .orderExecReportBroadcast message => OrderExecReportBroadcast.encode message
  | .orderExecResponse message => OrderExecResponse.encode message
  | .quoteExecReportBroadcast message => QuoteExecReportBroadcast.encode message
  | .quoteExecutionReport message => QuoteExecutionReport.encode message
  | .reject message => Reject.encode message
  | .retransmitMeMessageResponse message => RetransmitMeMessageResponse.encode message
  | .retransmitResponse message => RetransmitResponse.encode message
  | .riskCollateralAlertAdminBroadcast message => RiskCollateralAlertAdminBroadcast.encode message
  | .riskCollateralAlertBroadcast message => RiskCollateralAlertBroadcast.encode message
  | .riskNotificationBroadcast message => RiskNotificationBroadcast.encode message
  | .serviceAvailabilityBroadcast message => ServiceAvailabilityBroadcast.encode message
  | .sessionPasswordChangeResponse message => SessionPasswordChangeResponse.encode message
  | .sessionRegistrationResponse message => SessionRegistrationResponse.encode message
  | .subscribeResponse message => SubscribeResponse.encode message
  | .tmTradingSessionStatusBroadcast message => TmTradingSessionStatusBroadcast.encode message
  | .throttleUpdateNotification message => ThrottleUpdateNotification.encode message
  | .tradeBroadcast message => TradeBroadcast.encode message
  | .tradeEnhancementBroadcast message => TradeEnhancementBroadcast.encode message
  | .tradingSessionStatusBroadcast message => TradingSessionStatusBroadcast.encode message
  | .unsubscribeResponse message => UnsubscribeResponse.encode message
  | .userLoginResponse message => UserLoginResponse.encode message
  | .userLogoutResponse message => UserLogoutResponse.encode message
  | .userPasswordChangeResponse message => UserPasswordChangeResponse.encode message

/-- Decoded from the whole of the frame: a message that reads to its end takes it all, any other must leave nothing -/
def decode (tag : BitVec 16) (bytes : List UInt8) : Option ServerPayload :=
  if tag = 10032 then (BroadcastErrorNotification.decode bytes).map fun message => .broadcastErrorNotification message
  else if tag = 10391 then (DebtInquiryResponse.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.debtInquiryResponse message) else none
  else if tag = 10122 then (DeleteAllOrderBroadcast.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.deleteAllOrderBroadcast message) else none
  else if tag = 10124 then (DeleteAllOrderNrResponse.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.deleteAllOrderNrResponse message) else none
  else if tag = 10308 then (DeleteAllOrderQuoteEventBroadcast.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.deleteAllOrderQuoteEventBroadcast message) else none
  else if tag = 10121 then (DeleteAllOrderResponse.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.deleteAllOrderResponse message) else none
  else if tag = 10410 then (DeleteAllQuoteBroadcast.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.deleteAllQuoteBroadcast message) else none
  else if tag = 10409 then (DeleteAllQuoteResponse.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.deleteAllQuoteResponse message) else none
  else if tag = 10112 then (DeleteOrderBroadcast.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.deleteOrderBroadcast message) else none
  else if tag = 10111 then (DeleteOrderNrResponse.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.deleteOrderNrResponse message) else none
  else if tag = 10110 then (DeleteOrderResponse.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.deleteOrderResponse message) else none
  else if tag = 10012 then (ForcedLogoutNotification.decode bytes).map fun message => .forcedLogoutNotification message
  else if tag = 10022 then (GatewayResponse.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.gatewayResponse message) else none
  else if tag = 10990 then (GwOrderAcknowledgement.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.gwOrderAcknowledgement message) else none
  else if tag = 10023 then (HeartbeatNotification.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.heartbeatNotification message) else none
  else if tag = 10036 then (InquireSessionListResponse.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.inquireSessionListResponse message) else none
  else if tag = 10001 then (LogonResponse.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.logonResponse message) else none
  else if tag = 10003 then (LogoutResponse.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.logoutResponse message) else none
  else if tag = 10406 then (MassQuoteResponse.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.massQuoteResponse message) else none
  else if tag = 10108 then (ModifyOrderNrResponse.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.modifyOrderNrResponse message) else none
  else if tag = 10107 then (ModifyOrderResponse.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.modifyOrderResponse message) else none
  else if tag = 10994 then (MultiLegExecReportBroadcast.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.multiLegExecReportBroadcast message) else none
  else if tag = 10993 then (MultiLegExecResponse.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.multiLegExecResponse message) else none
  else if tag = 10992 then (MultiLegOrderReject.decode bytes).map fun message => .multiLegOrderReject message
  else if tag = 10102 then (NewOrderNrResponse.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.newOrderNrResponse message) else none
  else if tag = 10101 then (NewOrderResponse.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.newOrderResponse message) else none
  else if tag = 10031 then (NewsBroadcast.decode bytes).map fun message => .newsBroadcast message
  else if tag = 10104 then (OrderExecNotification.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.orderExecNotification message) else none
  else if tag = 10117 then (OrderExecReportBroadcast.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.orderExecReportBroadcast message) else none
  else if tag = 10103 then (OrderExecResponse.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.orderExecResponse message) else none
  else if tag = 10412 then (QuoteExecReportBroadcast.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.quoteExecReportBroadcast message) else none
  else if tag = 10407 then (QuoteExecutionReport.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.quoteExecutionReport message) else none
  else if tag = 10010 then (Reject.decode bytes).map fun message => .reject message
  else if tag = 10027 then (RetransmitMeMessageResponse.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.retransmitMeMessageResponse message) else none
  else if tag = 10009 then (RetransmitResponse.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.retransmitResponse message) else none
  else if tag = 10048 then (RiskCollateralAlertAdminBroadcast.decode bytes).map fun message => .riskCollateralAlertAdminBroadcast message
  else if tag = 10049 then (RiskCollateralAlertBroadcast.decode bytes).map fun message => .riskCollateralAlertBroadcast message
  else if tag = 10033 then (RiskNotificationBroadcast.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.riskNotificationBroadcast message) else none
  else if tag = 10030 then (ServiceAvailabilityBroadcast.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.serviceAvailabilityBroadcast message) else none
  else if tag = 10995 then (SessionPasswordChangeResponse.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.sessionPasswordChangeResponse message) else none
  else if tag = 10054 then (SessionRegistrationResponse.decode bytes).map fun message => .sessionRegistrationResponse message
  else if tag = 10005 then (SubscribeResponse.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.subscribeResponse message) else none
  else if tag = 10501 then (TmTradingSessionStatusBroadcast.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.tmTradingSessionStatusBroadcast message) else none
  else if tag = 10028 then (ThrottleUpdateNotification.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.throttleUpdateNotification message) else none
  else if tag = 10500 then (TradeBroadcast.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.tradeBroadcast message) else none
  else if tag = 10989 then (TradeEnhancementBroadcast.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.tradeEnhancementBroadcast message) else none
  else if tag = 10307 then (TradingSessionStatusBroadcast.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.tradingSessionStatusBroadcast message) else none
  else if tag = 10007 then (UnsubscribeResponse.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.unsubscribeResponse message) else none
  else if tag = 10019 then (UserLoginResponse.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.userLoginResponse message) else none
  else if tag = 10024 then (UserLogoutResponse.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.userLogoutResponse message) else none
  else if tag = 10043 then (UserPasswordChangeResponse.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.userPasswordChangeResponse message) else none
  else none

theorem decode_encode (message : ServerPayload) :
    decode (tag message) (encode message) = some message := by
  cases message with
  | broadcastErrorNotification message => simp [decode, encode, tag, BroadcastErrorNotification.decode_encode]
  | debtInquiryResponse message => simp [decode, encode, tag, DebtInquiryResponse.decode_encode_nil]
  | deleteAllOrderBroadcast message => simp [decode, encode, tag, DeleteAllOrderBroadcast.decode_encode_nil]
  | deleteAllOrderNrResponse message => simp [decode, encode, tag, DeleteAllOrderNrResponse.decode_encode_nil]
  | deleteAllOrderQuoteEventBroadcast message => simp [decode, encode, tag, DeleteAllOrderQuoteEventBroadcast.decode_encode_nil]
  | deleteAllOrderResponse message => simp [decode, encode, tag, DeleteAllOrderResponse.decode_encode_nil]
  | deleteAllQuoteBroadcast message => simp [decode, encode, tag, DeleteAllQuoteBroadcast.decode_encode_nil]
  | deleteAllQuoteResponse message => simp [decode, encode, tag, DeleteAllQuoteResponse.decode_encode_nil]
  | deleteOrderBroadcast message => simp [decode, encode, tag, DeleteOrderBroadcast.decode_encode_nil]
  | deleteOrderNrResponse message => simp [decode, encode, tag, DeleteOrderNrResponse.decode_encode_nil]
  | deleteOrderResponse message => simp [decode, encode, tag, DeleteOrderResponse.decode_encode_nil]
  | forcedLogoutNotification message => simp [decode, encode, tag, ForcedLogoutNotification.decode_encode]
  | gatewayResponse message => simp [decode, encode, tag, GatewayResponse.decode_encode_nil]
  | gwOrderAcknowledgement message => simp [decode, encode, tag, GwOrderAcknowledgement.decode_encode_nil]
  | heartbeatNotification message => simp [decode, encode, tag, HeartbeatNotification.decode_encode_nil]
  | inquireSessionListResponse message => simp [decode, encode, tag, InquireSessionListResponse.decode_encode_nil]
  | logonResponse message => simp [decode, encode, tag, LogonResponse.decode_encode_nil]
  | logoutResponse message => simp [decode, encode, tag, LogoutResponse.decode_encode_nil]
  | massQuoteResponse message => simp [decode, encode, tag, MassQuoteResponse.decode_encode_nil]
  | modifyOrderNrResponse message => simp [decode, encode, tag, ModifyOrderNrResponse.decode_encode_nil]
  | modifyOrderResponse message => simp [decode, encode, tag, ModifyOrderResponse.decode_encode_nil]
  | multiLegExecReportBroadcast message => simp [decode, encode, tag, MultiLegExecReportBroadcast.decode_encode_nil]
  | multiLegExecResponse message => simp [decode, encode, tag, MultiLegExecResponse.decode_encode_nil]
  | multiLegOrderReject message => simp [decode, encode, tag, MultiLegOrderReject.decode_encode]
  | newOrderNrResponse message => simp [decode, encode, tag, NewOrderNrResponse.decode_encode_nil]
  | newOrderResponse message => simp [decode, encode, tag, NewOrderResponse.decode_encode_nil]
  | newsBroadcast message => simp [decode, encode, tag, NewsBroadcast.decode_encode]
  | orderExecNotification message => simp [decode, encode, tag, OrderExecNotification.decode_encode_nil]
  | orderExecReportBroadcast message => simp [decode, encode, tag, OrderExecReportBroadcast.decode_encode_nil]
  | orderExecResponse message => simp [decode, encode, tag, OrderExecResponse.decode_encode_nil]
  | quoteExecReportBroadcast message => simp [decode, encode, tag, QuoteExecReportBroadcast.decode_encode_nil]
  | quoteExecutionReport message => simp [decode, encode, tag, QuoteExecutionReport.decode_encode_nil]
  | reject message => simp [decode, encode, tag, Reject.decode_encode]
  | retransmitMeMessageResponse message => simp [decode, encode, tag, RetransmitMeMessageResponse.decode_encode_nil]
  | retransmitResponse message => simp [decode, encode, tag, RetransmitResponse.decode_encode_nil]
  | riskCollateralAlertAdminBroadcast message => simp [decode, encode, tag, RiskCollateralAlertAdminBroadcast.decode_encode]
  | riskCollateralAlertBroadcast message => simp [decode, encode, tag, RiskCollateralAlertBroadcast.decode_encode]
  | riskNotificationBroadcast message => simp [decode, encode, tag, RiskNotificationBroadcast.decode_encode_nil]
  | serviceAvailabilityBroadcast message => simp [decode, encode, tag, ServiceAvailabilityBroadcast.decode_encode_nil]
  | sessionPasswordChangeResponse message => simp [decode, encode, tag, SessionPasswordChangeResponse.decode_encode_nil]
  | sessionRegistrationResponse message => simp [decode, encode, tag, SessionRegistrationResponse.decode_encode]
  | subscribeResponse message => simp [decode, encode, tag, SubscribeResponse.decode_encode_nil]
  | tmTradingSessionStatusBroadcast message => simp [decode, encode, tag, TmTradingSessionStatusBroadcast.decode_encode_nil]
  | throttleUpdateNotification message => simp [decode, encode, tag, ThrottleUpdateNotification.decode_encode_nil]
  | tradeBroadcast message => simp [decode, encode, tag, TradeBroadcast.decode_encode_nil]
  | tradeEnhancementBroadcast message => simp [decode, encode, tag, TradeEnhancementBroadcast.decode_encode_nil]
  | tradingSessionStatusBroadcast message => simp [decode, encode, tag, TradingSessionStatusBroadcast.decode_encode_nil]
  | unsubscribeResponse message => simp [decode, encode, tag, UnsubscribeResponse.decode_encode_nil]
  | userLoginResponse message => simp [decode, encode, tag, UserLoginResponse.decode_encode_nil]
  | userLogoutResponse message => simp [decode, encode, tag, UserLogoutResponse.decode_encode_nil]
  | userPasswordChangeResponse message => simp [decode, encode, tag, UserPasswordChangeResponse.decode_encode_nil]

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
  | broadcastErrorNotification inner =>
    have bound_inner := BroadcastErrorNotification.encode_length_le inner
    simp only [ServerPayload.encode, List.length_append, encodeUIntLE_length]
    omega
  | debtInquiryResponse inner =>
    simp only [ServerPayload.encode, List.length_append, encodeUIntLE_length, DebtInquiryResponse.encode_length]
    omega
  | deleteAllOrderBroadcast inner =>
    have bound_inner := DeleteAllOrderBroadcast.encode_length_le inner
    simp only [ServerPayload.encode, List.length_append, encodeUIntLE_length]
    omega
  | deleteAllOrderNrResponse inner =>
    simp only [ServerPayload.encode, List.length_append, encodeUIntLE_length, DeleteAllOrderNrResponse.encode_length]
    omega
  | deleteAllOrderQuoteEventBroadcast inner =>
    simp only [ServerPayload.encode, List.length_append, encodeUIntLE_length, DeleteAllOrderQuoteEventBroadcast.encode_length]
    omega
  | deleteAllOrderResponse inner =>
    have bound_inner := DeleteAllOrderResponse.encode_length_le inner
    simp only [ServerPayload.encode, List.length_append, encodeUIntLE_length]
    omega
  | deleteAllQuoteBroadcast inner =>
    have bound_inner := DeleteAllQuoteBroadcast.encode_length_le inner
    simp only [ServerPayload.encode, List.length_append, encodeUIntLE_length]
    omega
  | deleteAllQuoteResponse inner =>
    have bound_inner := DeleteAllQuoteResponse.encode_length_le inner
    simp only [ServerPayload.encode, List.length_append, encodeUIntLE_length]
    omega
  | deleteOrderBroadcast inner =>
    simp only [ServerPayload.encode, List.length_append, encodeUIntLE_length, DeleteOrderBroadcast.encode_length]
    omega
  | deleteOrderNrResponse inner =>
    simp only [ServerPayload.encode, List.length_append, encodeUIntLE_length, DeleteOrderNrResponse.encode_length]
    omega
  | deleteOrderResponse inner =>
    simp only [ServerPayload.encode, List.length_append, encodeUIntLE_length, DeleteOrderResponse.encode_length]
    omega
  | forcedLogoutNotification inner =>
    have bound_inner := ForcedLogoutNotification.encode_length_le inner
    simp only [ServerPayload.encode, List.length_append, encodeUIntLE_length]
    omega
  | gatewayResponse inner =>
    simp only [ServerPayload.encode, List.length_append, encodeUIntLE_length, GatewayResponse.encode_length]
    omega
  | gwOrderAcknowledgement inner =>
    simp only [ServerPayload.encode, List.length_append, encodeUIntLE_length, GwOrderAcknowledgement.encode_length]
    omega
  | heartbeatNotification inner =>
    simp only [ServerPayload.encode, List.length_append, encodeUIntLE_length, HeartbeatNotification.encode_length]
    omega
  | inquireSessionListResponse inner =>
    have bound_inner := InquireSessionListResponse.encode_length_le inner
    simp only [ServerPayload.encode, List.length_append, encodeUIntLE_length]
    omega
  | logonResponse inner =>
    simp only [ServerPayload.encode, List.length_append, encodeUIntLE_length, LogonResponse.encode_length]
    omega
  | logoutResponse inner =>
    simp only [ServerPayload.encode, List.length_append, encodeUIntLE_length, LogoutResponse.encode_length]
    omega
  | massQuoteResponse inner =>
    have bound_inner := MassQuoteResponse.encode_length_le inner
    simp only [ServerPayload.encode, List.length_append, encodeUIntLE_length]
    omega
  | modifyOrderNrResponse inner =>
    simp only [ServerPayload.encode, List.length_append, encodeUIntLE_length, ModifyOrderNrResponse.encode_length]
    omega
  | modifyOrderResponse inner =>
    simp only [ServerPayload.encode, List.length_append, encodeUIntLE_length, ModifyOrderResponse.encode_length]
    omega
  | multiLegExecReportBroadcast inner =>
    have bound_inner := MultiLegExecReportBroadcast.encode_length_le inner
    simp only [ServerPayload.encode, List.length_append, encodeUIntLE_length]
    omega
  | multiLegExecResponse inner =>
    have bound_inner := MultiLegExecResponse.encode_length_le inner
    simp only [ServerPayload.encode, List.length_append, encodeUIntLE_length]
    omega
  | multiLegOrderReject inner =>
    have bound_inner := MultiLegOrderReject.encode_length_le inner
    simp only [ServerPayload.encode, List.length_append, encodeUIntLE_length]
    omega
  | newOrderNrResponse inner =>
    simp only [ServerPayload.encode, List.length_append, encodeUIntLE_length, NewOrderNrResponse.encode_length]
    omega
  | newOrderResponse inner =>
    simp only [ServerPayload.encode, List.length_append, encodeUIntLE_length, NewOrderResponse.encode_length]
    omega
  | newsBroadcast inner =>
    have bound_inner := NewsBroadcast.encode_length_le inner
    simp only [ServerPayload.encode, List.length_append, encodeUIntLE_length]
    omega
  | orderExecNotification inner =>
    have bound_inner := OrderExecNotification.encode_length_le inner
    simp only [ServerPayload.encode, List.length_append, encodeUIntLE_length]
    omega
  | orderExecReportBroadcast inner =>
    have bound_inner := OrderExecReportBroadcast.encode_length_le inner
    simp only [ServerPayload.encode, List.length_append, encodeUIntLE_length]
    omega
  | orderExecResponse inner =>
    have bound_inner := OrderExecResponse.encode_length_le inner
    simp only [ServerPayload.encode, List.length_append, encodeUIntLE_length]
    omega
  | quoteExecReportBroadcast inner =>
    have bound_inner := QuoteExecReportBroadcast.encode_length_le inner
    simp only [ServerPayload.encode, List.length_append, encodeUIntLE_length]
    omega
  | quoteExecutionReport inner =>
    have bound_inner := QuoteExecutionReport.encode_length_le inner
    simp only [ServerPayload.encode, List.length_append, encodeUIntLE_length]
    omega
  | reject inner =>
    have bound_inner := Reject.encode_length_le inner
    simp only [ServerPayload.encode, List.length_append, encodeUIntLE_length]
    omega
  | retransmitMeMessageResponse inner =>
    simp only [ServerPayload.encode, List.length_append, encodeUIntLE_length, RetransmitMeMessageResponse.encode_length]
    omega
  | retransmitResponse inner =>
    simp only [ServerPayload.encode, List.length_append, encodeUIntLE_length, RetransmitResponse.encode_length]
    omega
  | riskCollateralAlertAdminBroadcast inner =>
    have bound_inner := RiskCollateralAlertAdminBroadcast.encode_length_le inner
    simp only [ServerPayload.encode, List.length_append, encodeUIntLE_length]
    omega
  | riskCollateralAlertBroadcast inner =>
    have bound_inner := RiskCollateralAlertBroadcast.encode_length_le inner
    simp only [ServerPayload.encode, List.length_append, encodeUIntLE_length]
    omega
  | riskNotificationBroadcast inner =>
    simp only [ServerPayload.encode, List.length_append, encodeUIntLE_length, RiskNotificationBroadcast.encode_length]
    omega
  | serviceAvailabilityBroadcast inner =>
    simp only [ServerPayload.encode, List.length_append, encodeUIntLE_length, ServiceAvailabilityBroadcast.encode_length]
    omega
  | sessionPasswordChangeResponse inner =>
    simp only [ServerPayload.encode, List.length_append, encodeUIntLE_length, SessionPasswordChangeResponse.encode_length]
    omega
  | sessionRegistrationResponse inner =>
    have bound_inner := SessionRegistrationResponse.encode_length_le inner
    simp only [ServerPayload.encode, List.length_append, encodeUIntLE_length]
    omega
  | subscribeResponse inner =>
    simp only [ServerPayload.encode, List.length_append, encodeUIntLE_length, SubscribeResponse.encode_length]
    omega
  | tmTradingSessionStatusBroadcast inner =>
    simp only [ServerPayload.encode, List.length_append, encodeUIntLE_length, TmTradingSessionStatusBroadcast.encode_length]
    omega
  | throttleUpdateNotification inner =>
    simp only [ServerPayload.encode, List.length_append, encodeUIntLE_length, ThrottleUpdateNotification.encode_length]
    omega
  | tradeBroadcast inner =>
    simp only [ServerPayload.encode, List.length_append, encodeUIntLE_length, TradeBroadcast.encode_length]
    omega
  | tradeEnhancementBroadcast inner =>
    simp only [ServerPayload.encode, List.length_append, encodeUIntLE_length, TradeEnhancementBroadcast.encode_length]
    omega
  | tradingSessionStatusBroadcast inner =>
    simp only [ServerPayload.encode, List.length_append, encodeUIntLE_length, TradingSessionStatusBroadcast.encode_length]
    omega
  | unsubscribeResponse inner =>
    simp only [ServerPayload.encode, List.length_append, encodeUIntLE_length, UnsubscribeResponse.encode_length]
    omega
  | userLoginResponse inner =>
    simp only [ServerPayload.encode, List.length_append, encodeUIntLE_length, UserLoginResponse.encode_length]
    omega
  | userLogoutResponse inner =>
    simp only [ServerPayload.encode, List.length_append, encodeUIntLE_length, UserLogoutResponse.encode_length]
    omega
  | userPasswordChangeResponse inner =>
    simp only [ServerPayload.encode, List.length_append, encodeUIntLE_length, UserPasswordChangeResponse.encode_length]
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

end Omi.BseBseindiaEtiFbeV1614Server
