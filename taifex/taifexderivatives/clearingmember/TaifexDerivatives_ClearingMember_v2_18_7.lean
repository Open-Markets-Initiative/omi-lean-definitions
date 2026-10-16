import Wire

/-!
# Taiwan Futures Exchange Clearing Member Order And Execution Report v2.18.7

Generated from the binary model, with the proofs the model's rules call for: every record
decodes back to what was encoded; a message dispatch selects the message its type names;
a count is written from the list it counts; a length prefix is written from the bytes it frames;
and a packet read to the end of its data decodes to the messages that were written.

Text fields are kept byte for byte, padding included, so what is decoded encodes back unchanged.
Prices with implied decimals are proven as the integers on the wire.
-/

namespace Omi.TaifexTaifexderivativesClearingmemberTmpV2187

/-- Exec Type: one byte code -/
def ExecType.codes : List UInt8 :=
  [0x30, 0x34, 0x35, 0x36, 0x46, 0x49, 0x4D, 0x6D]

inductive ExecType where
  | new -- New
  | cancel -- Cancel
  | decrease -- Decrease
  | newAndExecutionReport -- New And Execution Report
  | executionReport -- Execution Report
  | query -- Query
  | modifyPriceReplyingToTheModifyingLine -- Modify Price Replying To The Modifying Line
  | modifyPriceReplyingToTheOriginalLine -- Modify Price Replying To The Original Line
  | unlisted (byte : { byte : UInt8 // byte ∉ ExecType.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace ExecType

def toByte : ExecType → UInt8
  | .new => 0x30
  | .cancel => 0x34
  | .decrease => 0x35
  | .newAndExecutionReport => 0x36
  | .executionReport => 0x46
  | .query => 0x49
  | .modifyPriceReplyingToTheModifyingLine => 0x4D
  | .modifyPriceReplyingToTheOriginalLine => 0x6D
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : ExecType :=
  if byte = 0x30 then .new
  else if byte = 0x34 then .cancel
  else if byte = 0x35 then .decrease
  else if byte = 0x36 then .newAndExecutionReport
  else if byte = 0x46 then .executionReport
  else if byte = 0x49 then .query
  else if byte = 0x4D then .modifyPriceReplyingToTheModifyingLine
  else .modifyPriceReplyingToTheOriginalLine

def ofByte (byte : UInt8) : ExecType :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : ExecType) : ofByte value.toByte = value := by
  cases value with
  | new => decide
  | cancel => decide
  | decrease => decide
  | newAndExecutionReport => decide
  | executionReport => decide
  | query => decide
  | modifyPriceReplyingToTheModifyingLine => decide
  | modifyPriceReplyingToTheOriginalLine => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : ExecType) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (ExecType × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : ExecType) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : ExecType) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : ExecType) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end ExecType

/-- Position Effect: one byte code -/
def PositionEffect.codes : List UInt8 :=
  [0x4F, 0x43, 0x44, 0x41, 0x37, 0x39]

inductive PositionEffect where
  | open_ -- Open
  | close -- Close
  | daytrade -- Daytrade
  | openAndSpecifiedPositionOffsets -- Open And Specified Position Offsets
  | offsetByFcm -- Offset By Fcm
  | marketMakerQuote -- Market Maker Quote
  | unlisted (byte : { byte : UInt8 // byte ∉ PositionEffect.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace PositionEffect

def toByte : PositionEffect → UInt8
  | .open_ => 0x4F
  | .close => 0x43
  | .daytrade => 0x44
  | .openAndSpecifiedPositionOffsets => 0x41
  | .offsetByFcm => 0x37
  | .marketMakerQuote => 0x39
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : PositionEffect :=
  if byte = 0x4F then .open_
  else if byte = 0x43 then .close
  else if byte = 0x44 then .daytrade
  else if byte = 0x41 then .openAndSpecifiedPositionOffsets
  else if byte = 0x37 then .offsetByFcm
  else .marketMakerQuote

def ofByte (byte : UInt8) : PositionEffect :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : PositionEffect) : ofByte value.toByte = value := by
  cases value with
  | open_ => decide
  | close => decide
  | daytrade => decide
  | openAndSpecifiedPositionOffsets => decide
  | offsetByFcm => decide
  | marketMakerQuote => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : PositionEffect) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (PositionEffect × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : PositionEffect) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : PositionEffect) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : PositionEffect) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end PositionEffect

/-- Header Time: 6 bytes -/
structure HeaderTime where
  headerEpochS : BitVec 32
  headerMs : BitVec 16
  deriving DecidableEq, Repr

namespace HeaderTime

def encode (message : HeaderTime) : List UInt8 :=
  encodeUInt 4 message.headerEpochS
    ++ (encodeUInt 2 message.headerMs)

def decode (bytes : List UInt8) : Option (HeaderTime × List UInt8) := do
  let (headerEpochS, bytes) ← decodeUInt 4 bytes
  let (headerMs, bytes) ← decodeUInt 2 bytes
  pure ({ headerEpochS, headerMs }, bytes)

@[simp] theorem encode_length (message : HeaderTime) : (encode message).length = 6 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length]

theorem encode_length_pos (message : HeaderTime) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : HeaderTime) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end HeaderTime

/-- Wake Up Call Message: 5 bytes -/
structure WakeUpCallMessage where
  statuscodeUint81 : BitVec 8
  startinboundnum : BitVec 32
  deriving DecidableEq, Repr

namespace WakeUpCallMessage

def encode (message : WakeUpCallMessage) : List UInt8 :=
  encodeUInt 1 message.statuscodeUint81
    ++ (encodeUInt 4 message.startinboundnum)

def decode (bytes : List UInt8) : Option (WakeUpCallMessage × List UInt8) := do
  let (statuscodeUint81, bytes) ← decodeUInt 1 bytes
  let (startinboundnum, bytes) ← decodeUInt 4 bytes
  pure ({ statuscodeUint81, startinboundnum }, bytes)

@[simp] theorem encode_length (message : WakeUpCallMessage) : (encode message).length = 5 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length]

theorem encode_length_pos (message : WakeUpCallMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : WakeUpCallMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end WakeUpCallMessage

/-- Wake Up Call Confirmed Message: 1 bytes -/
structure WakeUpCallConfirmedMessage where
  version : BitVec 8
  deriving DecidableEq, Repr

namespace WakeUpCallConfirmedMessage

def encode (message : WakeUpCallConfirmedMessage) : List UInt8 :=
  encodeUInt 1 message.version

def decode (bytes : List UInt8) : Option (WakeUpCallConfirmedMessage × List UInt8) := do
  let (version, bytes) ← decodeUInt 1 bytes
  pure ({ version }, bytes)

@[simp] theorem encode_length (message : WakeUpCallConfirmedMessage) : (encode message).length = 1 := by
  unfold encode
  simp only [encodeUInt_length]

theorem encode_length_pos (message : WakeUpCallConfirmedMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : WakeUpCallConfirmedMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end WakeUpCallConfirmedMessage

/-- Logon Notice Message: 9 bytes -/
structure LogonNoticeMessage where
  statuscodeUint81 : BitVec 8
  appendno : BitVec 16
  endoutboundnum : BitVec 32
  systemtype : BitVec 8
  encryptMethod : BitVec 8
  deriving DecidableEq, Repr

namespace LogonNoticeMessage

def encode (message : LogonNoticeMessage) : List UInt8 :=
  encodeUInt 1 message.statuscodeUint81
    ++ (encodeUInt 2 message.appendno
    ++ (encodeUInt 4 message.endoutboundnum
    ++ (encodeUInt 1 message.systemtype
    ++ (encodeUInt 1 message.encryptMethod))))

def decode (bytes : List UInt8) : Option (LogonNoticeMessage × List UInt8) := do
  let (statuscodeUint81, bytes) ← decodeUInt 1 bytes
  let (appendno, bytes) ← decodeUInt 2 bytes
  let (endoutboundnum, bytes) ← decodeUInt 4 bytes
  let (systemtype, bytes) ← decodeUInt 1 bytes
  let (encryptMethod, bytes) ← decodeUInt 1 bytes
  pure ({ statuscodeUint81, appendno, endoutboundnum, systemtype, encryptMethod }, bytes)

@[simp] theorem encode_length (message : LogonNoticeMessage) : (encode message).length = 9 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length]

theorem encode_length_pos (message : LogonNoticeMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : LogonNoticeMessage) (rest : List UInt8) :
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
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end LogonNoticeMessage

/-- Subhdr: 6 bytes -/
structure Subhdr where
  msgTypeExt : BitVec 8
  preserve : BitVec 8
  msgtimens : BitVec 32
  deriving DecidableEq, Repr

namespace Subhdr

def encode (message : Subhdr) : List UInt8 :=
  encodeUInt 1 message.msgTypeExt
    ++ (encodeUInt 1 message.preserve
    ++ (encodeUInt 4 message.msgtimens))

def decode (bytes : List UInt8) : Option (Subhdr × List UInt8) := do
  let (msgTypeExt, bytes) ← decodeUInt 1 bytes
  let (preserve, bytes) ← decodeUInt 1 bytes
  let (msgtimens, bytes) ← decodeUInt 4 bytes
  pure ({ msgTypeExt, preserve, msgtimens }, bytes)

@[simp] theorem encode_length (message : Subhdr) : (encode message).length = 6 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length]

theorem encode_length_pos (message : Subhdr) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : Subhdr) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end Subhdr

/-- Final Sequential Number Notification For Group Message: 21 bytes -/
structure FinalSequentialNumberNotificationForGroupMessage where
  subhdr : Subhdr
  statuscodeUint162 : BitVec 16
  partid : BitVec 8
  endoutboundnum : BitVec 32
  reserved8 : Alpha 8
  deriving DecidableEq, Repr

namespace FinalSequentialNumberNotificationForGroupMessage

def encode (message : FinalSequentialNumberNotificationForGroupMessage) : List UInt8 :=
  Subhdr.encode message.subhdr
    ++ (encodeUInt 2 message.statuscodeUint162
    ++ (encodeUInt 1 message.partid
    ++ (encodeUInt 4 message.endoutboundnum
    ++ (Alpha.encode message.reserved8))))

def decode (bytes : List UInt8) : Option (FinalSequentialNumberNotificationForGroupMessage × List UInt8) := do
  let (subhdr, bytes) ← Subhdr.decode bytes
  let (statuscodeUint162, bytes) ← decodeUInt 2 bytes
  let (partid, bytes) ← decodeUInt 1 bytes
  let (endoutboundnum, bytes) ← decodeUInt 4 bytes
  let (reserved8, bytes) ← Alpha.decode 8 bytes
  pure ({ subhdr, statuscodeUint162, partid, endoutboundnum, reserved8 }, bytes)

@[simp] theorem encode_length (message : FinalSequentialNumberNotificationForGroupMessage) : (encode message).length = 21 := by
  unfold encode
  simp only [List.length_append, Subhdr.encode_length, encodeUInt_length, Alpha.encode_length]

theorem encode_length_pos (message : FinalSequentialNumberNotificationForGroupMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : FinalSequentialNumberNotificationForGroupMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Subhdr.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end FinalSequentialNumberNotificationForGroupMessage

/-- Request Logon Message: 15 bytes -/
structure RequestLogonMessage where
  statuscodeUint81 : BitVec 8
  appendno : BitVec 16
  fcmid : BitVec 16
  sessionid : BitVec 16
  systemtype : BitVec 8
  apcode : BitVec 8
  keyvalue : BitVec 8
  requeststartseq : BitVec 32
  cancelordersec : BitVec 8
  deriving DecidableEq, Repr

namespace RequestLogonMessage

def encode (message : RequestLogonMessage) : List UInt8 :=
  encodeUInt 1 message.statuscodeUint81
    ++ (encodeUInt 2 message.appendno
    ++ (encodeUInt 2 message.fcmid
    ++ (encodeUInt 2 message.sessionid
    ++ (encodeUInt 1 message.systemtype
    ++ (encodeUInt 1 message.apcode
    ++ (encodeUInt 1 message.keyvalue
    ++ (encodeUInt 4 message.requeststartseq
    ++ (encodeUInt 1 message.cancelordersec))))))))

def decode (bytes : List UInt8) : Option (RequestLogonMessage × List UInt8) := do
  let (statuscodeUint81, bytes) ← decodeUInt 1 bytes
  let (appendno, bytes) ← decodeUInt 2 bytes
  let (fcmid, bytes) ← decodeUInt 2 bytes
  let (sessionid, bytes) ← decodeUInt 2 bytes
  let (systemtype, bytes) ← decodeUInt 1 bytes
  let (apcode, bytes) ← decodeUInt 1 bytes
  let (keyvalue, bytes) ← decodeUInt 1 bytes
  let (requeststartseq, bytes) ← decodeUInt 4 bytes
  let (cancelordersec, bytes) ← decodeUInt 1 bytes
  pure ({ statuscodeUint81, appendno, fcmid, sessionid, systemtype, apcode, keyvalue, requeststartseq, cancelordersec }, bytes)

@[simp] theorem encode_length (message : RequestLogonMessage) : (encode message).length = 15 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length]

theorem encode_length_pos (message : RequestLogonMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : RequestLogonMessage) (rest : List UInt8) :
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

end RequestLogonMessage

/-- Activate Application System Message: 4 bytes -/
structure ActivateApplicationSystemMessage where
  statuscodeUint81 : BitVec 8
  heartBtInt : BitVec 8
  maxflowctrlcnt : BitVec 16
  deriving DecidableEq, Repr

namespace ActivateApplicationSystemMessage

def encode (message : ActivateApplicationSystemMessage) : List UInt8 :=
  encodeUInt 1 message.statuscodeUint81
    ++ (encodeUInt 1 message.heartBtInt
    ++ (encodeUInt 2 message.maxflowctrlcnt))

def decode (bytes : List UInt8) : Option (ActivateApplicationSystemMessage × List UInt8) := do
  let (statuscodeUint81, bytes) ← decodeUInt 1 bytes
  let (heartBtInt, bytes) ← decodeUInt 1 bytes
  let (maxflowctrlcnt, bytes) ← decodeUInt 2 bytes
  pure ({ statuscodeUint81, heartBtInt, maxflowctrlcnt }, bytes)

@[simp] theorem encode_length (message : ActivateApplicationSystemMessage) : (encode message).length = 4 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length]

theorem encode_length_pos (message : ActivateApplicationSystemMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : ActivateApplicationSystemMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end ActivateApplicationSystemMessage

/-- Activate Application System Confirmed Message: 1 bytes -/
structure ActivateApplicationSystemConfirmedMessage where
  statuscodeUint81 : BitVec 8
  deriving DecidableEq, Repr

namespace ActivateApplicationSystemConfirmedMessage

def encode (message : ActivateApplicationSystemConfirmedMessage) : List UInt8 :=
  encodeUInt 1 message.statuscodeUint81

def decode (bytes : List UInt8) : Option (ActivateApplicationSystemConfirmedMessage × List UInt8) := do
  let (statuscodeUint81, bytes) ← decodeUInt 1 bytes
  pure ({ statuscodeUint81 }, bytes)

@[simp] theorem encode_length (message : ActivateApplicationSystemConfirmedMessage) : (encode message).length = 1 := by
  unfold encode
  simp only [encodeUInt_length]

theorem encode_length_pos (message : ActivateApplicationSystemConfirmedMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : ActivateApplicationSystemConfirmedMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end ActivateApplicationSystemConfirmedMessage

/-- Logout Message: 0 bytes -/
structure LogoutMessage where
  deriving DecidableEq, Repr

namespace LogoutMessage

def encode (_ : LogoutMessage) : List UInt8 :=
  []

def decode (bytes : List UInt8) : Option (LogoutMessage × List UInt8) :=
  some (⟨⟩, bytes)

@[simp] theorem encode_length (message : LogoutMessage) : (encode message).length = 0 := by
  simp [encode]

@[simp] theorem decode_encode (message : LogoutMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  simp [decode, encode]

end LogoutMessage

/-- Logout Confirmed Message: 1 bytes -/
structure LogoutConfirmedMessage where
  statuscodeUint81 : BitVec 8
  deriving DecidableEq, Repr

namespace LogoutConfirmedMessage

def encode (message : LogoutConfirmedMessage) : List UInt8 :=
  encodeUInt 1 message.statuscodeUint81

def decode (bytes : List UInt8) : Option (LogoutConfirmedMessage × List UInt8) := do
  let (statuscodeUint81, bytes) ← decodeUInt 1 bytes
  pure ({ statuscodeUint81 }, bytes)

@[simp] theorem encode_length (message : LogoutConfirmedMessage) : (encode message).length = 1 := by
  unfold encode
  simp only [encodeUInt_length]

theorem encode_length_pos (message : LogoutConfirmedMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : LogoutConfirmedMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end LogoutConfirmedMessage

/-- Confirm Connection Message: 1 bytes -/
structure ConfirmConnectionMessage where
  statuscodeUint81 : BitVec 8
  deriving DecidableEq, Repr

namespace ConfirmConnectionMessage

def encode (message : ConfirmConnectionMessage) : List UInt8 :=
  encodeUInt 1 message.statuscodeUint81

def decode (bytes : List UInt8) : Option (ConfirmConnectionMessage × List UInt8) := do
  let (statuscodeUint81, bytes) ← decodeUInt 1 bytes
  pure ({ statuscodeUint81 }, bytes)

@[simp] theorem encode_length (message : ConfirmConnectionMessage) : (encode message).length = 1 := by
  unfold encode
  simp only [encodeUInt_length]

theorem encode_length_pos (message : ConfirmConnectionMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : ConfirmConnectionMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end ConfirmConnectionMessage

/-- Connection Confirmed Message: 1 bytes -/
structure ConnectionConfirmedMessage where
  statuscodeUint81 : BitVec 8
  deriving DecidableEq, Repr

namespace ConnectionConfirmedMessage

def encode (message : ConnectionConfirmedMessage) : List UInt8 :=
  encodeUInt 1 message.statuscodeUint81

def decode (bytes : List UInt8) : Option (ConnectionConfirmedMessage × List UInt8) := do
  let (statuscodeUint81, bytes) ← decodeUInt 1 bytes
  pure ({ statuscodeUint81 }, bytes)

@[simp] theorem encode_length (message : ConnectionConfirmedMessage) : (encode message).length = 1 := by
  unfold encode
  simp only [encodeUInt_length]

theorem encode_length_pos (message : ConnectionConfirmedMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : ConnectionConfirmedMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end ConnectionConfirmedMessage

/-- Symbolnum: 19 bytes -/
structure Symbolnum where
  pseq1 : BitVec 16
  pseq2 : BitVec 16
  legsideUint822 : BitVec 8
  combop : BitVec 8
  reserved13 : Alpha 13
  deriving DecidableEq, Repr

namespace Symbolnum

def encode (message : Symbolnum) : List UInt8 :=
  encodeUInt 2 message.pseq1
    ++ (encodeUInt 2 message.pseq2
    ++ (encodeUInt 1 message.legsideUint822
    ++ (encodeUInt 1 message.combop
    ++ (Alpha.encode message.reserved13))))

def decode (bytes : List UInt8) : Option (Symbolnum × List UInt8) := do
  let (pseq1, bytes) ← decodeUInt 2 bytes
  let (pseq2, bytes) ← decodeUInt 2 bytes
  let (legsideUint822, bytes) ← decodeUInt 1 bytes
  let (combop, bytes) ← decodeUInt 1 bytes
  let (reserved13, bytes) ← Alpha.decode 13 bytes
  pure ({ pseq1, pseq2, legsideUint822, combop, reserved13 }, bytes)

@[simp] theorem encode_length (message : Symbolnum) : (encode message).length = 19 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Alpha.encode_length]

theorem encode_length_pos (message : Symbolnum) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : Symbolnum) (rest : List UInt8) :
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
  rw [Alpha.decode_encode, some_bind]
  rfl

end Symbolnum

/-- Symboltext: 20 bytes -/
structure Symboltext where
  symbolChar2020 : Alpha 20
  deriving DecidableEq, Repr

namespace Symboltext

def encode (message : Symboltext) : List UInt8 :=
  Alpha.encode message.symbolChar2020

def decode (bytes : List UInt8) : Option (Symboltext × List UInt8) := do
  let (symbolChar2020, bytes) ← Alpha.decode 20 bytes
  pure ({ symbolChar2020 }, bytes)

@[simp] theorem encode_length (message : Symboltext) : (encode message).length = 20 := by
  unfold encode
  simp only [Alpha.encode_length]

theorem encode_length_pos (message : Symboltext) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : Symboltext) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [Alpha.decode_encode, some_bind]
  rfl

end Symboltext

/-- Any Sym Symbolx, selected by Symboltype -/
inductive SymSymbolx where
  | symbolnum (message : Symbolnum) -- 1
  | symboltext (message : Symboltext) -- 2
  deriving DecidableEq, Repr

namespace SymSymbolx

/-- The Symboltype each message is sent under -/
def tag : SymSymbolx → BitVec 8
  | .symbolnum _ => 1
  | .symboltext _ => 2

def encode : SymSymbolx → List UInt8
  | .symbolnum message => Symbolnum.encode message
  | .symboltext message => Symboltext.encode message

/-- The most bytes any message's encoding can take -/
theorem encode_length_le (message : SymSymbolx) : (encode message).length ≤ 20 := by
  cases message with
  | symbolnum inner =>
    simp only [encode, Symbolnum.encode_length]
    omega
  | symboltext inner =>
    simp only [encode, Symboltext.encode_length]
    omega

def decode (tag : BitVec 8) (bytes : List UInt8) : Option (SymSymbolx × List UInt8) :=
  if tag = 1 then (Symbolnum.decode bytes).map fun (message, rest) => (.symbolnum message, rest)
  else if tag = 2 then (Symboltext.decode bytes).map fun (message, rest) => (.symboltext message, rest)
  else none

@[simp] theorem decode_encode (message : SymSymbolx) (rest : List UInt8) :
    decode (tag message) (encode message ++ rest) = some (message, rest) := by
  cases message <;> simp [decode, encode, tag]

end SymSymbolx

/-- Orgtranstime Msgtime: 6 bytes -/
structure OrgtranstimeMsgtime where
  epochsInt324 : BitVec 32
  ms : BitVec 16
  deriving DecidableEq, Repr

namespace OrgtranstimeMsgtime

def encode (message : OrgtranstimeMsgtime) : List UInt8 :=
  encodeUInt 4 message.epochsInt324
    ++ (encodeUInt 2 message.ms)

def decode (bytes : List UInt8) : Option (OrgtranstimeMsgtime × List UInt8) := do
  let (epochsInt324, bytes) ← decodeUInt 4 bytes
  let (ms, bytes) ← decodeUInt 2 bytes
  pure ({ epochsInt324, ms }, bytes)

@[simp] theorem encode_length (message : OrgtranstimeMsgtime) : (encode message).length = 6 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length]

theorem encode_length_pos (message : OrgtranstimeMsgtime) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OrgtranstimeMsgtime) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end OrgtranstimeMsgtime

/-- Transact Time Msgtime: 6 bytes -/
structure TransactTimeMsgtime where
  epochsInt324 : BitVec 32
  ms : BitVec 16
  deriving DecidableEq, Repr

namespace TransactTimeMsgtime

def encode (message : TransactTimeMsgtime) : List UInt8 :=
  encodeUInt 4 message.epochsInt324
    ++ (encodeUInt 2 message.ms)

def decode (bytes : List UInt8) : Option (TransactTimeMsgtime × List UInt8) := do
  let (epochsInt324, bytes) ← decodeUInt 4 bytes
  let (ms, bytes) ← decodeUInt 2 bytes
  pure ({ epochsInt324, ms }, bytes)

@[simp] theorem encode_length (message : TransactTimeMsgtime) : (encode message).length = 6 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length]

theorem encode_length_pos (message : TransactTimeMsgtime) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : TransactTimeMsgtime) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end TransactTimeMsgtime

/-- Order Status Report Message -/
structure OrderStatusReportMessage where
  statuscodeUint81 : BitVec 8
  execType : ExecType
  cmid : BitVec 16
  fcmid : BitVec 16
  orderno : Alpha 5
  ordid : BitVec 32
  userdefine : Alpha 8
  symSymbolx : SymSymbolx
  price : BitVec 32
  qty : BitVec 16
  investoracno : BitVec 32
  investorflag : Alpha 1
  side : BitVec 8
  ordType : BitVec 8
  timeInForce : BitVec 8
  positionEffect : PositionEffect
  lastPx : BitVec 32
  lastQty : BitVec 16
  pxsubtotal : BitVec 64
  cumQty : BitVec 16
  leavesQty : BitVec 16
  beforeqty : BitVec 16
  legsideUint822 : BitVec 8
  legpx : BitVec 32
  legqtyUint1624 : BitVec 16
  orgtranstimeMsgtime : OrgtranstimeMsgtime
  transactTimeMsgtime : TransactTimeMsgtime
  targetid : BitVec 8
  uniqid : BitVec 32
  rptseq : BitVec 32
  protocoltype : BitVec 8
  deriving DecidableEq, Repr

namespace OrderStatusReportMessage

def encode (message : OrderStatusReportMessage) : List UInt8 :=
  encodeUInt 1 message.statuscodeUint81
    ++ (ExecType.encode message.execType
    ++ (encodeUInt 2 message.cmid
    ++ (encodeUInt 2 message.fcmid
    ++ (Alpha.encode message.orderno
    ++ (encodeUInt 4 message.ordid
    ++ (Alpha.encode message.userdefine
    ++ (encodeUInt 1 (SymSymbolx.tag message.symSymbolx)
    ++ (SymSymbolx.encode message.symSymbolx
    ++ (encodeUInt 4 message.price
    ++ (encodeUInt 2 message.qty
    ++ (encodeUInt 4 message.investoracno
    ++ (Alpha.encode message.investorflag
    ++ (encodeUInt 1 message.side
    ++ (encodeUInt 1 message.ordType
    ++ (encodeUInt 1 message.timeInForce
    ++ (PositionEffect.encode message.positionEffect
    ++ (encodeUInt 4 message.lastPx
    ++ (encodeUInt 2 message.lastQty
    ++ (encodeUInt 8 message.pxsubtotal
    ++ (encodeUInt 2 message.cumQty
    ++ (encodeUInt 2 message.leavesQty
    ++ (encodeUInt 2 message.beforeqty
    ++ (encodeUInt 1 message.legsideUint822
    ++ (encodeUInt 4 message.legpx
    ++ (encodeUInt 2 message.legqtyUint1624
    ++ (OrgtranstimeMsgtime.encode message.orgtranstimeMsgtime
    ++ (TransactTimeMsgtime.encode message.transactTimeMsgtime
    ++ (encodeUInt 1 message.targetid
    ++ (encodeUInt 4 message.uniqid
    ++ (encodeUInt 4 message.rptseq
    ++ (encodeUInt 1 message.protocoltype)))))))))))))))))))))))))))))))

-- a long run of fields nests deeper than the elaborator's default limit
set_option maxRecDepth 4096 in
def decode (bytes : List UInt8) : Option (OrderStatusReportMessage × List UInt8) := do
  let (statuscodeUint81, bytes) ← decodeUInt 1 bytes
  let (execType, bytes) ← ExecType.decode bytes
  let (cmid, bytes) ← decodeUInt 2 bytes
  let (fcmid, bytes) ← decodeUInt 2 bytes
  let (orderno, bytes) ← Alpha.decode 5 bytes
  let (ordid, bytes) ← decodeUInt 4 bytes
  let (userdefine, bytes) ← Alpha.decode 8 bytes
  let (symboltype, bytes) ← decodeUInt 1 bytes
  let (symSymbolx, bytes) ← SymSymbolx.decode symboltype bytes
  let (price, bytes) ← decodeUInt 4 bytes
  let (qty, bytes) ← decodeUInt 2 bytes
  let (investoracno, bytes) ← decodeUInt 4 bytes
  let (investorflag, bytes) ← Alpha.decode 1 bytes
  let (side, bytes) ← decodeUInt 1 bytes
  let (ordType, bytes) ← decodeUInt 1 bytes
  let (timeInForce, bytes) ← decodeUInt 1 bytes
  let (positionEffect, bytes) ← PositionEffect.decode bytes
  let (lastPx, bytes) ← decodeUInt 4 bytes
  let (lastQty, bytes) ← decodeUInt 2 bytes
  let (pxsubtotal, bytes) ← decodeUInt 8 bytes
  let (cumQty, bytes) ← decodeUInt 2 bytes
  let (leavesQty, bytes) ← decodeUInt 2 bytes
  let (beforeqty, bytes) ← decodeUInt 2 bytes
  let (legsideUint822, bytes) ← decodeUInt 1 bytes
  let (legpx, bytes) ← decodeUInt 4 bytes
  let (legqtyUint1624, bytes) ← decodeUInt 2 bytes
  let (orgtranstimeMsgtime, bytes) ← OrgtranstimeMsgtime.decode bytes
  let (transactTimeMsgtime, bytes) ← TransactTimeMsgtime.decode bytes
  let (targetid, bytes) ← decodeUInt 1 bytes
  let (uniqid, bytes) ← decodeUInt 4 bytes
  let (rptseq, bytes) ← decodeUInt 4 bytes
  let (protocoltype, bytes) ← decodeUInt 1 bytes
  pure ({ statuscodeUint81, execType, cmid, fcmid, orderno, ordid, userdefine, symSymbolx, price, qty, investoracno, investorflag, side, ordType, timeInForce, positionEffect, lastPx, lastQty, pxsubtotal, cumQty, leavesQty, beforeqty, legsideUint822, legpx, legqtyUint1624, orgtranstimeMsgtime, transactTimeMsgtime, targetid, uniqid, rptseq, protocoltype }, bytes)

theorem encode_length_pos (message : OrderStatusReportMessage) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUInt_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : OrderStatusReportMessage) : (encode message).length ≤ 108 := by
  unfold encode
  cases message.symSymbolx with
  | symbolnum inner =>
    simp only [SymSymbolx.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, ExecType.encode_length, Alpha.encode_length, PositionEffect.encode_length, OrgtranstimeMsgtime.encode_length, TransactTimeMsgtime.encode_length, Symbolnum.encode_length]
    omega
  | symboltext inner =>
    simp only [SymSymbolx.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, ExecType.encode_length, Alpha.encode_length, PositionEffect.encode_length, OrgtranstimeMsgtime.encode_length, TransactTimeMsgtime.encode_length, Symboltext.encode_length]
    omega

set_option maxRecDepth 4096 in
@[simp] theorem decode_encode (message : OrderStatusReportMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, ExecType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, SymSymbolx.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
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
  rw [List.append_assoc, PositionEffect.decode_encode, some_bind]
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
  rw [List.append_assoc, OrgtranstimeMsgtime.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, TransactTimeMsgtime.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end OrderStatusReportMessage

/-- Longsymbolnum: 39 bytes -/
structure Longsymbolnum where
  pseq1 : BitVec 16
  pseq2 : BitVec 16
  legsideUint822 : BitVec 8
  combop : BitVec 8
  reserved33 : Alpha 33
  deriving DecidableEq, Repr

namespace Longsymbolnum

def encode (message : Longsymbolnum) : List UInt8 :=
  encodeUInt 2 message.pseq1
    ++ (encodeUInt 2 message.pseq2
    ++ (encodeUInt 1 message.legsideUint822
    ++ (encodeUInt 1 message.combop
    ++ (Alpha.encode message.reserved33))))

def decode (bytes : List UInt8) : Option (Longsymbolnum × List UInt8) := do
  let (pseq1, bytes) ← decodeUInt 2 bytes
  let (pseq2, bytes) ← decodeUInt 2 bytes
  let (legsideUint822, bytes) ← decodeUInt 1 bytes
  let (combop, bytes) ← decodeUInt 1 bytes
  let (reserved33, bytes) ← Alpha.decode 33 bytes
  pure ({ pseq1, pseq2, legsideUint822, combop, reserved33 }, bytes)

@[simp] theorem encode_length (message : Longsymbolnum) : (encode message).length = 39 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Alpha.encode_length]

theorem encode_length_pos (message : Longsymbolnum) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : Longsymbolnum) (rest : List UInt8) :
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
  rw [Alpha.decode_encode, some_bind]
  rfl

end Longsymbolnum

/-- Longsymboltext: 40 bytes -/
structure Longsymboltext where
  symbolChar4040 : Alpha 40
  deriving DecidableEq, Repr

namespace Longsymboltext

def encode (message : Longsymboltext) : List UInt8 :=
  Alpha.encode message.symbolChar4040

def decode (bytes : List UInt8) : Option (Longsymboltext × List UInt8) := do
  let (symbolChar4040, bytes) ← Alpha.decode 40 bytes
  pure ({ symbolChar4040 }, bytes)

@[simp] theorem encode_length (message : Longsymboltext) : (encode message).length = 40 := by
  unfold encode
  simp only [Alpha.encode_length]

theorem encode_length_pos (message : Longsymboltext) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : Longsymboltext) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [Alpha.decode_encode, some_bind]
  rfl

end Longsymboltext

/-- Any Sym Longsymbolx, selected by Symboltype -/
inductive SymLongsymbolx where
  | longsymbolnum (message : Longsymbolnum) -- 3
  | longsymboltext (message : Longsymboltext) -- 4
  deriving DecidableEq, Repr

namespace SymLongsymbolx

/-- The Symboltype each message is sent under -/
def tag : SymLongsymbolx → BitVec 8
  | .longsymbolnum _ => 3
  | .longsymboltext _ => 4

def encode : SymLongsymbolx → List UInt8
  | .longsymbolnum message => Longsymbolnum.encode message
  | .longsymboltext message => Longsymboltext.encode message

/-- The most bytes any message's encoding can take -/
theorem encode_length_le (message : SymLongsymbolx) : (encode message).length ≤ 40 := by
  cases message with
  | longsymbolnum inner =>
    simp only [encode, Longsymbolnum.encode_length]
    omega
  | longsymboltext inner =>
    simp only [encode, Longsymboltext.encode_length]
    omega

def decode (tag : BitVec 8) (bytes : List UInt8) : Option (SymLongsymbolx × List UInt8) :=
  if tag = 3 then (Longsymbolnum.decode bytes).map fun (message, rest) => (.longsymbolnum message, rest)
  else if tag = 4 then (Longsymboltext.decode bytes).map fun (message, rest) => (.longsymboltext message, rest)
  else none

@[simp] theorem decode_encode (message : SymLongsymbolx) (rest : List UInt8) :
    decode (tag message) (encode message ++ rest) = some (message, rest) := by
  cases message <;> simp [decode, encode, tag]

end SymLongsymbolx

/-- Order Status Report Long Format Message -/
structure OrderStatusReportLongFormatMessage where
  statuscodeUint81 : BitVec 8
  execType : ExecType
  cmid : BitVec 16
  fcmid : BitVec 16
  orderno : Alpha 5
  ordid : BitVec 32
  userdefine : Alpha 8
  symLongsymbolx : SymLongsymbolx
  price : BitVec 32
  qty : BitVec 16
  investoracno : BitVec 32
  investorflag : Alpha 1
  side : BitVec 8
  ordType : BitVec 8
  timeInForce : BitVec 8
  positionEffect : PositionEffect
  lastPx : BitVec 32
  lastQty : BitVec 16
  pxsubtotal : BitVec 64
  cumQty : BitVec 16
  leavesQty : BitVec 16
  beforeqty : BitVec 16
  legsideUint822 : BitVec 8
  legpx : BitVec 32
  legqtyUint1624 : BitVec 16
  orgtranstimeMsgtime : OrgtranstimeMsgtime
  transactTimeMsgtime : TransactTimeMsgtime
  targetid : BitVec 8
  uniqid : BitVec 32
  rptseq : BitVec 32
  protocoltype : BitVec 8
  deriving DecidableEq, Repr

namespace OrderStatusReportLongFormatMessage

def encode (message : OrderStatusReportLongFormatMessage) : List UInt8 :=
  encodeUInt 1 message.statuscodeUint81
    ++ (ExecType.encode message.execType
    ++ (encodeUInt 2 message.cmid
    ++ (encodeUInt 2 message.fcmid
    ++ (Alpha.encode message.orderno
    ++ (encodeUInt 4 message.ordid
    ++ (Alpha.encode message.userdefine
    ++ (encodeUInt 1 (SymLongsymbolx.tag message.symLongsymbolx)
    ++ (SymLongsymbolx.encode message.symLongsymbolx
    ++ (encodeUInt 4 message.price
    ++ (encodeUInt 2 message.qty
    ++ (encodeUInt 4 message.investoracno
    ++ (Alpha.encode message.investorflag
    ++ (encodeUInt 1 message.side
    ++ (encodeUInt 1 message.ordType
    ++ (encodeUInt 1 message.timeInForce
    ++ (PositionEffect.encode message.positionEffect
    ++ (encodeUInt 4 message.lastPx
    ++ (encodeUInt 2 message.lastQty
    ++ (encodeUInt 8 message.pxsubtotal
    ++ (encodeUInt 2 message.cumQty
    ++ (encodeUInt 2 message.leavesQty
    ++ (encodeUInt 2 message.beforeqty
    ++ (encodeUInt 1 message.legsideUint822
    ++ (encodeUInt 4 message.legpx
    ++ (encodeUInt 2 message.legqtyUint1624
    ++ (OrgtranstimeMsgtime.encode message.orgtranstimeMsgtime
    ++ (TransactTimeMsgtime.encode message.transactTimeMsgtime
    ++ (encodeUInt 1 message.targetid
    ++ (encodeUInt 4 message.uniqid
    ++ (encodeUInt 4 message.rptseq
    ++ (encodeUInt 1 message.protocoltype)))))))))))))))))))))))))))))))

-- a long run of fields nests deeper than the elaborator's default limit
set_option maxRecDepth 4096 in
def decode (bytes : List UInt8) : Option (OrderStatusReportLongFormatMessage × List UInt8) := do
  let (statuscodeUint81, bytes) ← decodeUInt 1 bytes
  let (execType, bytes) ← ExecType.decode bytes
  let (cmid, bytes) ← decodeUInt 2 bytes
  let (fcmid, bytes) ← decodeUInt 2 bytes
  let (orderno, bytes) ← Alpha.decode 5 bytes
  let (ordid, bytes) ← decodeUInt 4 bytes
  let (userdefine, bytes) ← Alpha.decode 8 bytes
  let (symboltype, bytes) ← decodeUInt 1 bytes
  let (symLongsymbolx, bytes) ← SymLongsymbolx.decode symboltype bytes
  let (price, bytes) ← decodeUInt 4 bytes
  let (qty, bytes) ← decodeUInt 2 bytes
  let (investoracno, bytes) ← decodeUInt 4 bytes
  let (investorflag, bytes) ← Alpha.decode 1 bytes
  let (side, bytes) ← decodeUInt 1 bytes
  let (ordType, bytes) ← decodeUInt 1 bytes
  let (timeInForce, bytes) ← decodeUInt 1 bytes
  let (positionEffect, bytes) ← PositionEffect.decode bytes
  let (lastPx, bytes) ← decodeUInt 4 bytes
  let (lastQty, bytes) ← decodeUInt 2 bytes
  let (pxsubtotal, bytes) ← decodeUInt 8 bytes
  let (cumQty, bytes) ← decodeUInt 2 bytes
  let (leavesQty, bytes) ← decodeUInt 2 bytes
  let (beforeqty, bytes) ← decodeUInt 2 bytes
  let (legsideUint822, bytes) ← decodeUInt 1 bytes
  let (legpx, bytes) ← decodeUInt 4 bytes
  let (legqtyUint1624, bytes) ← decodeUInt 2 bytes
  let (orgtranstimeMsgtime, bytes) ← OrgtranstimeMsgtime.decode bytes
  let (transactTimeMsgtime, bytes) ← TransactTimeMsgtime.decode bytes
  let (targetid, bytes) ← decodeUInt 1 bytes
  let (uniqid, bytes) ← decodeUInt 4 bytes
  let (rptseq, bytes) ← decodeUInt 4 bytes
  let (protocoltype, bytes) ← decodeUInt 1 bytes
  pure ({ statuscodeUint81, execType, cmid, fcmid, orderno, ordid, userdefine, symLongsymbolx, price, qty, investoracno, investorflag, side, ordType, timeInForce, positionEffect, lastPx, lastQty, pxsubtotal, cumQty, leavesQty, beforeqty, legsideUint822, legpx, legqtyUint1624, orgtranstimeMsgtime, transactTimeMsgtime, targetid, uniqid, rptseq, protocoltype }, bytes)

theorem encode_length_pos (message : OrderStatusReportLongFormatMessage) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUInt_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : OrderStatusReportLongFormatMessage) : (encode message).length ≤ 128 := by
  unfold encode
  cases message.symLongsymbolx with
  | longsymbolnum inner =>
    simp only [SymLongsymbolx.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, ExecType.encode_length, Alpha.encode_length, PositionEffect.encode_length, OrgtranstimeMsgtime.encode_length, TransactTimeMsgtime.encode_length, Longsymbolnum.encode_length]
    omega
  | longsymboltext inner =>
    simp only [SymLongsymbolx.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, ExecType.encode_length, Alpha.encode_length, PositionEffect.encode_length, OrgtranstimeMsgtime.encode_length, TransactTimeMsgtime.encode_length, Longsymboltext.encode_length]
    omega

set_option maxRecDepth 4096 in
@[simp] theorem decode_encode (message : OrderStatusReportLongFormatMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, ExecType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, SymLongsymbolx.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
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
  rw [List.append_assoc, PositionEffect.decode_encode, some_bind]
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
  rw [List.append_assoc, OrgtranstimeMsgtime.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, TransactTimeMsgtime.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end OrderStatusReportLongFormatMessage

/-- Execution Report Including Head Office And Branch Offices Message -/
structure ExecutionReportIncludingHeadOfficeAndBranchOfficesMessage where
  statuscodeUint81 : BitVec 8
  execType : ExecType
  cmid : BitVec 16
  fcmid : BitVec 16
  orderno : Alpha 5
  ordid : BitVec 32
  userdefine : Alpha 8
  symSymbolx : SymSymbolx
  price : BitVec 32
  qty : BitVec 16
  investoracno : BitVec 32
  investorflag : Alpha 1
  side : BitVec 8
  ordType : BitVec 8
  timeInForce : BitVec 8
  positionEffect : PositionEffect
  lastPx : BitVec 32
  lastQty : BitVec 16
  pxsubtotal : BitVec 64
  cumQty : BitVec 16
  leavesQty : BitVec 16
  beforeqty : BitVec 16
  legsideUint822 : BitVec 8
  legpx : BitVec 32
  legqtyUint1624 : BitVec 16
  orgtranstimeMsgtime : OrgtranstimeMsgtime
  transactTimeMsgtime : TransactTimeMsgtime
  targetid : BitVec 8
  uniqid : BitVec 32
  rptseq : BitVec 32
  protocoltype : BitVec 8
  rptsessionid : BitVec 16
  deriving DecidableEq, Repr

namespace ExecutionReportIncludingHeadOfficeAndBranchOfficesMessage

def encode (message : ExecutionReportIncludingHeadOfficeAndBranchOfficesMessage) : List UInt8 :=
  encodeUInt 1 message.statuscodeUint81
    ++ (ExecType.encode message.execType
    ++ (encodeUInt 2 message.cmid
    ++ (encodeUInt 2 message.fcmid
    ++ (Alpha.encode message.orderno
    ++ (encodeUInt 4 message.ordid
    ++ (Alpha.encode message.userdefine
    ++ (encodeUInt 1 (SymSymbolx.tag message.symSymbolx)
    ++ (SymSymbolx.encode message.symSymbolx
    ++ (encodeUInt 4 message.price
    ++ (encodeUInt 2 message.qty
    ++ (encodeUInt 4 message.investoracno
    ++ (Alpha.encode message.investorflag
    ++ (encodeUInt 1 message.side
    ++ (encodeUInt 1 message.ordType
    ++ (encodeUInt 1 message.timeInForce
    ++ (PositionEffect.encode message.positionEffect
    ++ (encodeUInt 4 message.lastPx
    ++ (encodeUInt 2 message.lastQty
    ++ (encodeUInt 8 message.pxsubtotal
    ++ (encodeUInt 2 message.cumQty
    ++ (encodeUInt 2 message.leavesQty
    ++ (encodeUInt 2 message.beforeqty
    ++ (encodeUInt 1 message.legsideUint822
    ++ (encodeUInt 4 message.legpx
    ++ (encodeUInt 2 message.legqtyUint1624
    ++ (OrgtranstimeMsgtime.encode message.orgtranstimeMsgtime
    ++ (TransactTimeMsgtime.encode message.transactTimeMsgtime
    ++ (encodeUInt 1 message.targetid
    ++ (encodeUInt 4 message.uniqid
    ++ (encodeUInt 4 message.rptseq
    ++ (encodeUInt 1 message.protocoltype
    ++ (encodeUInt 2 message.rptsessionid))))))))))))))))))))))))))))))))

-- a long run of fields nests deeper than the elaborator's default limit
set_option maxRecDepth 4096 in
def decode (bytes : List UInt8) : Option (ExecutionReportIncludingHeadOfficeAndBranchOfficesMessage × List UInt8) := do
  let (statuscodeUint81, bytes) ← decodeUInt 1 bytes
  let (execType, bytes) ← ExecType.decode bytes
  let (cmid, bytes) ← decodeUInt 2 bytes
  let (fcmid, bytes) ← decodeUInt 2 bytes
  let (orderno, bytes) ← Alpha.decode 5 bytes
  let (ordid, bytes) ← decodeUInt 4 bytes
  let (userdefine, bytes) ← Alpha.decode 8 bytes
  let (symboltype, bytes) ← decodeUInt 1 bytes
  let (symSymbolx, bytes) ← SymSymbolx.decode symboltype bytes
  let (price, bytes) ← decodeUInt 4 bytes
  let (qty, bytes) ← decodeUInt 2 bytes
  let (investoracno, bytes) ← decodeUInt 4 bytes
  let (investorflag, bytes) ← Alpha.decode 1 bytes
  let (side, bytes) ← decodeUInt 1 bytes
  let (ordType, bytes) ← decodeUInt 1 bytes
  let (timeInForce, bytes) ← decodeUInt 1 bytes
  let (positionEffect, bytes) ← PositionEffect.decode bytes
  let (lastPx, bytes) ← decodeUInt 4 bytes
  let (lastQty, bytes) ← decodeUInt 2 bytes
  let (pxsubtotal, bytes) ← decodeUInt 8 bytes
  let (cumQty, bytes) ← decodeUInt 2 bytes
  let (leavesQty, bytes) ← decodeUInt 2 bytes
  let (beforeqty, bytes) ← decodeUInt 2 bytes
  let (legsideUint822, bytes) ← decodeUInt 1 bytes
  let (legpx, bytes) ← decodeUInt 4 bytes
  let (legqtyUint1624, bytes) ← decodeUInt 2 bytes
  let (orgtranstimeMsgtime, bytes) ← OrgtranstimeMsgtime.decode bytes
  let (transactTimeMsgtime, bytes) ← TransactTimeMsgtime.decode bytes
  let (targetid, bytes) ← decodeUInt 1 bytes
  let (uniqid, bytes) ← decodeUInt 4 bytes
  let (rptseq, bytes) ← decodeUInt 4 bytes
  let (protocoltype, bytes) ← decodeUInt 1 bytes
  let (rptsessionid, bytes) ← decodeUInt 2 bytes
  pure ({ statuscodeUint81, execType, cmid, fcmid, orderno, ordid, userdefine, symSymbolx, price, qty, investoracno, investorflag, side, ordType, timeInForce, positionEffect, lastPx, lastQty, pxsubtotal, cumQty, leavesQty, beforeqty, legsideUint822, legpx, legqtyUint1624, orgtranstimeMsgtime, transactTimeMsgtime, targetid, uniqid, rptseq, protocoltype, rptsessionid }, bytes)

theorem encode_length_pos (message : ExecutionReportIncludingHeadOfficeAndBranchOfficesMessage) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUInt_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : ExecutionReportIncludingHeadOfficeAndBranchOfficesMessage) : (encode message).length ≤ 110 := by
  unfold encode
  cases message.symSymbolx with
  | symbolnum inner =>
    simp only [SymSymbolx.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, ExecType.encode_length, Alpha.encode_length, PositionEffect.encode_length, OrgtranstimeMsgtime.encode_length, TransactTimeMsgtime.encode_length, Symbolnum.encode_length]
    omega
  | symboltext inner =>
    simp only [SymSymbolx.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, ExecType.encode_length, Alpha.encode_length, PositionEffect.encode_length, OrgtranstimeMsgtime.encode_length, TransactTimeMsgtime.encode_length, Symboltext.encode_length]
    omega

set_option maxRecDepth 4096 in
@[simp] theorem decode_encode (message : ExecutionReportIncludingHeadOfficeAndBranchOfficesMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, ExecType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, SymSymbolx.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
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
  rw [List.append_assoc, PositionEffect.decode_encode, some_bind]
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
  rw [List.append_assoc, OrgtranstimeMsgtime.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, TransactTimeMsgtime.decode_encode, some_bind]
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

end ExecutionReportIncludingHeadOfficeAndBranchOfficesMessage

/-- Symbolnumx: 4 bytes -/
structure Symbolnumx where
  pseq : BitVec 32
  deriving DecidableEq, Repr

namespace Symbolnumx

def encode (message : Symbolnumx) : List UInt8 :=
  encodeUInt 4 message.pseq

def decode (bytes : List UInt8) : Option (Symbolnumx × List UInt8) := do
  let (pseq, bytes) ← decodeUInt 4 bytes
  pure ({ pseq }, bytes)

@[simp] theorem encode_length (message : Symbolnumx) : (encode message).length = 4 := by
  unfold encode
  simp only [encodeUInt_length]

theorem encode_length_pos (message : Symbolnumx) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : Symbolnumx) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end Symbolnumx

/-- Symboltxtx: 20 bytes -/
structure Symboltxtx where
  prodid : Alpha 20
  deriving DecidableEq, Repr

namespace Symboltxtx

def encode (message : Symboltxtx) : List UInt8 :=
  Alpha.encode message.prodid

def decode (bytes : List UInt8) : Option (Symboltxtx × List UInt8) := do
  let (prodid, bytes) ← Alpha.decode 20 bytes
  pure ({ prodid }, bytes)

@[simp] theorem encode_length (message : Symboltxtx) : (encode message).length = 20 := by
  unfold encode
  simp only [Alpha.encode_length]

theorem encode_length_pos (message : Symboltxtx) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : Symboltxtx) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [Alpha.decode_encode, some_bind]
  rfl

end Symboltxtx

/-- Legsym Symbolnumx: 4 bytes -/
structure LegsymSymbolnumx where
  pseq : BitVec 32
  deriving DecidableEq, Repr

namespace LegsymSymbolnumx

def encode (message : LegsymSymbolnumx) : List UInt8 :=
  encodeUInt 4 message.pseq

def decode (bytes : List UInt8) : Option (LegsymSymbolnumx × List UInt8) := do
  let (pseq, bytes) ← decodeUInt 4 bytes
  pure ({ pseq }, bytes)

@[simp] theorem encode_length (message : LegsymSymbolnumx) : (encode message).length = 4 := by
  unfold encode
  simp only [encodeUInt_length]

theorem encode_length_pos (message : LegsymSymbolnumx) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : LegsymSymbolnumx) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end LegsymSymbolnumx

/-- Legentrynum: 7 bytes -/
structure Legentrynum where
  legsymSymbolnumx : LegsymSymbolnumx
  legsideUint81 : BitVec 8
  legqtyUint162 : BitVec 16
  deriving DecidableEq, Repr

namespace Legentrynum

def encode (message : Legentrynum) : List UInt8 :=
  LegsymSymbolnumx.encode message.legsymSymbolnumx
    ++ (encodeUInt 1 message.legsideUint81
    ++ (encodeUInt 2 message.legqtyUint162))

def decode (bytes : List UInt8) : Option (Legentrynum × List UInt8) := do
  let (legsymSymbolnumx, bytes) ← LegsymSymbolnumx.decode bytes
  let (legsideUint81, bytes) ← decodeUInt 1 bytes
  let (legqtyUint162, bytes) ← decodeUInt 2 bytes
  pure ({ legsymSymbolnumx, legsideUint81, legqtyUint162 }, bytes)

@[simp] theorem encode_length (message : Legentrynum) : (encode message).length = 7 := by
  unfold encode
  simp only [List.length_append, LegsymSymbolnumx.encode_length, encodeUInt_length]

theorem encode_length_pos (message : Legentrynum) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : Legentrynum) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, LegsymSymbolnumx.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end Legentrynum

/-- Multilegnum -/
structure Multilegnum where
  combop : BitVec 8
  legentrynum : Bounded 1 Legentrynum
  deriving DecidableEq, Repr

namespace Multilegnum

def encode (message : Multilegnum) : List UInt8 :=
  encodeUInt 1 (BitVec.ofNat (8 * 1) message.legentrynum.val.length)
    ++ (encodeUInt 1 message.combop
    ++ (encodeMany Legentrynum.encode message.legentrynum.val))

def decode (bytes : List UInt8) : Option (Multilegnum × List UInt8) := do
  let (noLeg, bytes) ← decodeUInt 1 bytes
  let (combop, bytes) ← decodeUInt 1 bytes
  let (legentrynum_, bytes) ← decodeMany Legentrynum.decode noLeg.toNat bytes
  if fits_legentrynum : legentrynum_.length < 256 ^ 1 then
    pure ({ combop, legentrynum := ⟨legentrynum_, fits_legentrynum⟩ }, bytes)
  else none

theorem encode_length_pos (message : Multilegnum) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUInt_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : Multilegnum) : (encode message).length ≤ 1787 := by
  have bound_legentrynum := message.legentrynum.length_lt
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, encodeUInt_length, encodeMany_length_const Legentrynum.encode 7 Legentrynum.encode_length]
  omega

@[simp] theorem decode_encode (message : Multilegnum) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeMany_bounded 1 Legentrynum.encode Legentrynum.decode Legentrynum.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.legentrynum.length_lt]
  rfl

end Multilegnum

/-- Legsym Symboltxtx: 20 bytes -/
structure LegsymSymboltxtx where
  prodid : Alpha 20
  deriving DecidableEq, Repr

namespace LegsymSymboltxtx

def encode (message : LegsymSymboltxtx) : List UInt8 :=
  Alpha.encode message.prodid

def decode (bytes : List UInt8) : Option (LegsymSymboltxtx × List UInt8) := do
  let (prodid, bytes) ← Alpha.decode 20 bytes
  pure ({ prodid }, bytes)

@[simp] theorem encode_length (message : LegsymSymboltxtx) : (encode message).length = 20 := by
  unfold encode
  simp only [Alpha.encode_length]

theorem encode_length_pos (message : LegsymSymboltxtx) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : LegsymSymboltxtx) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [Alpha.decode_encode, some_bind]
  rfl

end LegsymSymboltxtx

/-- Legentrytxt: 23 bytes -/
structure Legentrytxt where
  legsymSymboltxtx : LegsymSymboltxtx
  legsideUint81 : BitVec 8
  legqtyUint162 : BitVec 16
  deriving DecidableEq, Repr

namespace Legentrytxt

def encode (message : Legentrytxt) : List UInt8 :=
  LegsymSymboltxtx.encode message.legsymSymboltxtx
    ++ (encodeUInt 1 message.legsideUint81
    ++ (encodeUInt 2 message.legqtyUint162))

def decode (bytes : List UInt8) : Option (Legentrytxt × List UInt8) := do
  let (legsymSymboltxtx, bytes) ← LegsymSymboltxtx.decode bytes
  let (legsideUint81, bytes) ← decodeUInt 1 bytes
  let (legqtyUint162, bytes) ← decodeUInt 2 bytes
  pure ({ legsymSymboltxtx, legsideUint81, legqtyUint162 }, bytes)

@[simp] theorem encode_length (message : Legentrytxt) : (encode message).length = 23 := by
  unfold encode
  simp only [List.length_append, LegsymSymboltxtx.encode_length, encodeUInt_length]

theorem encode_length_pos (message : Legentrytxt) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : Legentrytxt) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, LegsymSymboltxtx.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end Legentrytxt

/-- Multilegtxt -/
structure Multilegtxt where
  combop : BitVec 8
  legentrytxt : Bounded 1 Legentrytxt
  deriving DecidableEq, Repr

namespace Multilegtxt

def encode (message : Multilegtxt) : List UInt8 :=
  encodeUInt 1 (BitVec.ofNat (8 * 1) message.legentrytxt.val.length)
    ++ (encodeUInt 1 message.combop
    ++ (encodeMany Legentrytxt.encode message.legentrytxt.val))

def decode (bytes : List UInt8) : Option (Multilegtxt × List UInt8) := do
  let (noLeg, bytes) ← decodeUInt 1 bytes
  let (combop, bytes) ← decodeUInt 1 bytes
  let (legentrytxt_, bytes) ← decodeMany Legentrytxt.decode noLeg.toNat bytes
  if fits_legentrytxt : legentrytxt_.length < 256 ^ 1 then
    pure ({ combop, legentrytxt := ⟨legentrytxt_, fits_legentrytxt⟩ }, bytes)
  else none

theorem encode_length_pos (message : Multilegtxt) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUInt_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : Multilegtxt) : (encode message).length ≤ 5867 := by
  have bound_legentrytxt := message.legentrytxt.length_lt
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, encodeUInt_length, encodeMany_length_const Legentrytxt.encode 23 Legentrytxt.encode_length]
  omega

@[simp] theorem decode_encode (message : Multilegtxt) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeMany_bounded 1 Legentrytxt.encode Legentrytxt.decode Legentrytxt.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.legentrytxt.length_lt]
  rfl

end Multilegtxt

/-- Any Sym Flexproductx, selected by Msg Type Ext -/
inductive SymFlexproductx where
  | symbolnumx (message : Symbolnumx) -- 1
  | symboltxtx (message : Symboltxtx) -- 2
  | multilegnum (message : Multilegnum) -- 3
  | multilegtxt (message : Multilegtxt) -- 4
  deriving DecidableEq, Repr

namespace SymFlexproductx

/-- The Msg Type Ext each message is sent under -/
def tag : SymFlexproductx → BitVec 8
  | .symbolnumx _ => 1
  | .symboltxtx _ => 2
  | .multilegnum _ => 3
  | .multilegtxt _ => 4

def encode : SymFlexproductx → List UInt8
  | .symbolnumx message => Symbolnumx.encode message
  | .symboltxtx message => Symboltxtx.encode message
  | .multilegnum message => Multilegnum.encode message
  | .multilegtxt message => Multilegtxt.encode message

/-- The most bytes any message's encoding can take -/
theorem encode_length_le (message : SymFlexproductx) : (encode message).length ≤ 5867 := by
  cases message with
  | symbolnumx inner =>
    simp only [encode, Symbolnumx.encode_length]
    omega
  | symboltxtx inner =>
    simp only [encode, Symboltxtx.encode_length]
    omega
  | multilegnum inner =>
    have bound_inner := Multilegnum.encode_length_le inner
    simp only [encode]
    omega
  | multilegtxt inner =>
    have bound_inner := Multilegtxt.encode_length_le inner
    simp only [encode]
    omega

def decode (tag : BitVec 8) (bytes : List UInt8) : Option (SymFlexproductx × List UInt8) :=
  if tag = 1 then (Symbolnumx.decode bytes).map fun (message, rest) => (.symbolnumx message, rest)
  else if tag = 2 then (Symboltxtx.decode bytes).map fun (message, rest) => (.symboltxtx message, rest)
  else if tag = 3 then (Multilegnum.decode bytes).map fun (message, rest) => (.multilegnum message, rest)
  else if tag = 4 then (Multilegtxt.decode bytes).map fun (message, rest) => (.multilegtxt message, rest)
  else none

@[simp] theorem decode_encode (message : SymFlexproductx) (rest : List UInt8) :
    decode (tag message) (encode message ++ rest) = some (message, rest) := by
  cases message <;> simp [decode, encode, tag]

end SymFlexproductx

/-- Orgtranstime Msgtimex: 8 bytes -/
structure OrgtranstimeMsgtimex where
  epochsUint324 : BitVec 32
  nanosecond : BitVec 32
  deriving DecidableEq, Repr

namespace OrgtranstimeMsgtimex

def encode (message : OrgtranstimeMsgtimex) : List UInt8 :=
  encodeUInt 4 message.epochsUint324
    ++ (encodeUInt 4 message.nanosecond)

def decode (bytes : List UInt8) : Option (OrgtranstimeMsgtimex × List UInt8) := do
  let (epochsUint324, bytes) ← decodeUInt 4 bytes
  let (nanosecond, bytes) ← decodeUInt 4 bytes
  pure ({ epochsUint324, nanosecond }, bytes)

@[simp] theorem encode_length (message : OrgtranstimeMsgtimex) : (encode message).length = 8 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length]

theorem encode_length_pos (message : OrgtranstimeMsgtimex) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OrgtranstimeMsgtimex) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end OrgtranstimeMsgtimex

/-- Transact Time Msgtimex: 8 bytes -/
structure TransactTimeMsgtimex where
  epochsUint324 : BitVec 32
  nanosecond : BitVec 32
  deriving DecidableEq, Repr

namespace TransactTimeMsgtimex

def encode (message : TransactTimeMsgtimex) : List UInt8 :=
  encodeUInt 4 message.epochsUint324
    ++ (encodeUInt 4 message.nanosecond)

def decode (bytes : List UInt8) : Option (TransactTimeMsgtimex × List UInt8) := do
  let (epochsUint324, bytes) ← decodeUInt 4 bytes
  let (nanosecond, bytes) ← decodeUInt 4 bytes
  pure ({ epochsUint324, nanosecond }, bytes)

@[simp] theorem encode_length (message : TransactTimeMsgtimex) : (encode message).length = 8 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length]

theorem encode_length_pos (message : TransactTimeMsgtimex) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : TransactTimeMsgtimex) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end TransactTimeMsgtimex

/-- Flex Order Status Report Message -/
structure FlexOrderStatusReportMessage where
  preserve : BitVec 8
  msgtimens : BitVec 32
  partid : BitVec 8
  noLeg : BitVec 8
  statuscodeUint162 : BitVec 16
  execType : ExecType
  cmid : BitVec 16
  fcmid : BitVec 16
  orderno : Alpha 5
  ordid : BitVec 32
  userdefine : Alpha 8
  symFlexproductx : SymFlexproductx
  price : BitVec 32
  qty : BitVec 16
  investoracno : BitVec 32
  investorflag : Alpha 1
  side : BitVec 8
  ordType : BitVec 8
  timeInForce : BitVec 8
  positionEffect : PositionEffect
  lastPx : BitVec 32
  lastQty : BitVec 16
  pxsubtotal : BitVec 64
  cumQty : BitVec 16
  leavesQty : BitVec 16
  beforeqty : BitVec 16
  orgtranstimeMsgtimex : OrgtranstimeMsgtimex
  transactTimeMsgtimex : TransactTimeMsgtimex
  targetid : BitVec 8
  uniqid : BitVec 32
  rptseq : BitVec 32
  rptsessionid : BitVec 16
  rptsessionseq : BitVec 32
  reserved12 : Alpha 12
  deriving DecidableEq, Repr

namespace FlexOrderStatusReportMessage

def encode (message : FlexOrderStatusReportMessage) : List UInt8 :=
  encodeUInt 1 (SymFlexproductx.tag message.symFlexproductx)
    ++ (encodeUInt 1 message.preserve
    ++ (encodeUInt 4 message.msgtimens
    ++ (encodeUInt 1 message.partid
    ++ (encodeUInt 1 message.noLeg
    ++ (encodeUInt 2 message.statuscodeUint162
    ++ (ExecType.encode message.execType
    ++ (encodeUInt 2 message.cmid
    ++ (encodeUInt 2 message.fcmid
    ++ (Alpha.encode message.orderno
    ++ (encodeUInt 4 message.ordid
    ++ (Alpha.encode message.userdefine
    ++ (SymFlexproductx.encode message.symFlexproductx
    ++ (encodeUInt 4 message.price
    ++ (encodeUInt 2 message.qty
    ++ (encodeUInt 4 message.investoracno
    ++ (Alpha.encode message.investorflag
    ++ (encodeUInt 1 message.side
    ++ (encodeUInt 1 message.ordType
    ++ (encodeUInt 1 message.timeInForce
    ++ (PositionEffect.encode message.positionEffect
    ++ (encodeUInt 4 message.lastPx
    ++ (encodeUInt 2 message.lastQty
    ++ (encodeUInt 8 message.pxsubtotal
    ++ (encodeUInt 2 message.cumQty
    ++ (encodeUInt 2 message.leavesQty
    ++ (encodeUInt 2 message.beforeqty
    ++ (OrgtranstimeMsgtimex.encode message.orgtranstimeMsgtimex
    ++ (TransactTimeMsgtimex.encode message.transactTimeMsgtimex
    ++ (encodeUInt 1 message.targetid
    ++ (encodeUInt 4 message.uniqid
    ++ (encodeUInt 4 message.rptseq
    ++ (encodeUInt 2 message.rptsessionid
    ++ (encodeUInt 4 message.rptsessionseq
    ++ (Alpha.encode message.reserved12))))))))))))))))))))))))))))))))))

-- a long run of fields nests deeper than the elaborator's default limit
set_option maxRecDepth 4096 in
def decode (bytes : List UInt8) : Option (FlexOrderStatusReportMessage × List UInt8) := do
  let (msgTypeExt, bytes) ← decodeUInt 1 bytes
  let (preserve, bytes) ← decodeUInt 1 bytes
  let (msgtimens, bytes) ← decodeUInt 4 bytes
  let (partid, bytes) ← decodeUInt 1 bytes
  let (noLeg, bytes) ← decodeUInt 1 bytes
  let (statuscodeUint162, bytes) ← decodeUInt 2 bytes
  let (execType, bytes) ← ExecType.decode bytes
  let (cmid, bytes) ← decodeUInt 2 bytes
  let (fcmid, bytes) ← decodeUInt 2 bytes
  let (orderno, bytes) ← Alpha.decode 5 bytes
  let (ordid, bytes) ← decodeUInt 4 bytes
  let (userdefine, bytes) ← Alpha.decode 8 bytes
  let (symFlexproductx, bytes) ← SymFlexproductx.decode msgTypeExt bytes
  let (price, bytes) ← decodeUInt 4 bytes
  let (qty, bytes) ← decodeUInt 2 bytes
  let (investoracno, bytes) ← decodeUInt 4 bytes
  let (investorflag, bytes) ← Alpha.decode 1 bytes
  let (side, bytes) ← decodeUInt 1 bytes
  let (ordType, bytes) ← decodeUInt 1 bytes
  let (timeInForce, bytes) ← decodeUInt 1 bytes
  let (positionEffect, bytes) ← PositionEffect.decode bytes
  let (lastPx, bytes) ← decodeUInt 4 bytes
  let (lastQty, bytes) ← decodeUInt 2 bytes
  let (pxsubtotal, bytes) ← decodeUInt 8 bytes
  let (cumQty, bytes) ← decodeUInt 2 bytes
  let (leavesQty, bytes) ← decodeUInt 2 bytes
  let (beforeqty, bytes) ← decodeUInt 2 bytes
  let (orgtranstimeMsgtimex, bytes) ← OrgtranstimeMsgtimex.decode bytes
  let (transactTimeMsgtimex, bytes) ← TransactTimeMsgtimex.decode bytes
  let (targetid, bytes) ← decodeUInt 1 bytes
  let (uniqid, bytes) ← decodeUInt 4 bytes
  let (rptseq, bytes) ← decodeUInt 4 bytes
  let (rptsessionid, bytes) ← decodeUInt 2 bytes
  let (rptsessionseq, bytes) ← decodeUInt 4 bytes
  let (reserved12, bytes) ← Alpha.decode 12 bytes
  pure ({ preserve, msgtimens, partid, noLeg, statuscodeUint162, execType, cmid, fcmid, orderno, ordid, userdefine, symFlexproductx, price, qty, investoracno, investorflag, side, ordType, timeInForce, positionEffect, lastPx, lastQty, pxsubtotal, cumQty, leavesQty, beforeqty, orgtranstimeMsgtimex, transactTimeMsgtimex, targetid, uniqid, rptseq, rptsessionid, rptsessionseq, reserved12 }, bytes)

theorem encode_length_pos (message : FlexOrderStatusReportMessage) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUInt_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : FlexOrderStatusReportMessage) : (encode message).length ≤ 5977 := by
  unfold encode
  cases message.symFlexproductx with
  | symbolnumx inner =>
    simp only [SymFlexproductx.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, ExecType.encode_length, Alpha.encode_length, PositionEffect.encode_length, OrgtranstimeMsgtimex.encode_length, TransactTimeMsgtimex.encode_length, Symbolnumx.encode_length]
    omega
  | symboltxtx inner =>
    simp only [SymFlexproductx.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, ExecType.encode_length, Alpha.encode_length, PositionEffect.encode_length, OrgtranstimeMsgtimex.encode_length, TransactTimeMsgtimex.encode_length, Symboltxtx.encode_length]
    omega
  | multilegnum inner =>
    have bound_inner := Multilegnum.encode_length_le inner
    simp only [SymFlexproductx.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, ExecType.encode_length, Alpha.encode_length, PositionEffect.encode_length, OrgtranstimeMsgtimex.encode_length, TransactTimeMsgtimex.encode_length]
    omega
  | multilegtxt inner =>
    have bound_inner := Multilegtxt.encode_length_le inner
    simp only [SymFlexproductx.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, ExecType.encode_length, Alpha.encode_length, PositionEffect.encode_length, OrgtranstimeMsgtimex.encode_length, TransactTimeMsgtimex.encode_length]
    omega

set_option maxRecDepth 4096 in
@[simp] theorem decode_encode (message : FlexOrderStatusReportMessage) (rest : List UInt8) :
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
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, ExecType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, SymFlexproductx.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
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
  rw [List.append_assoc, PositionEffect.decode_encode, some_bind]
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
  rw [List.append_assoc, OrgtranstimeMsgtimex.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, TransactTimeMsgtimex.decode_encode, some_bind]
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
  rw [Alpha.decode_encode, some_bind]
  rfl

end FlexOrderStatusReportMessage

/-- Clearing Member Initiate Operation Message: 7 bytes -/
structure ClearingMemberInitiateOperationMessage where
  memberid : BitVec 16
  targetid : BitVec 8
  reqcmseq : BitVec 32
  deriving DecidableEq, Repr

namespace ClearingMemberInitiateOperationMessage

def encode (message : ClearingMemberInitiateOperationMessage) : List UInt8 :=
  encodeUInt 2 message.memberid
    ++ (encodeUInt 1 message.targetid
    ++ (encodeUInt 4 message.reqcmseq))

def decode (bytes : List UInt8) : Option (ClearingMemberInitiateOperationMessage × List UInt8) := do
  let (memberid, bytes) ← decodeUInt 2 bytes
  let (targetid, bytes) ← decodeUInt 1 bytes
  let (reqcmseq, bytes) ← decodeUInt 4 bytes
  pure ({ memberid, targetid, reqcmseq }, bytes)

@[simp] theorem encode_length (message : ClearingMemberInitiateOperationMessage) : (encode message).length = 7 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length]

theorem encode_length_pos (message : ClearingMemberInitiateOperationMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : ClearingMemberInitiateOperationMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end ClearingMemberInitiateOperationMessage

/-- Clearing Member Initiate Operation Confirmed Message: 8 bytes -/
structure ClearingMemberInitiateOperationConfirmedMessage where
  statuscodeUint81 : BitVec 8
  memberid : BitVec 16
  targetid : BitVec 8
  reqcmseq : BitVec 32
  deriving DecidableEq, Repr

namespace ClearingMemberInitiateOperationConfirmedMessage

def encode (message : ClearingMemberInitiateOperationConfirmedMessage) : List UInt8 :=
  encodeUInt 1 message.statuscodeUint81
    ++ (encodeUInt 2 message.memberid
    ++ (encodeUInt 1 message.targetid
    ++ (encodeUInt 4 message.reqcmseq)))

def decode (bytes : List UInt8) : Option (ClearingMemberInitiateOperationConfirmedMessage × List UInt8) := do
  let (statuscodeUint81, bytes) ← decodeUInt 1 bytes
  let (memberid, bytes) ← decodeUInt 2 bytes
  let (targetid, bytes) ← decodeUInt 1 bytes
  let (reqcmseq, bytes) ← decodeUInt 4 bytes
  pure ({ statuscodeUint81, memberid, targetid, reqcmseq }, bytes)

@[simp] theorem encode_length (message : ClearingMemberInitiateOperationConfirmedMessage) : (encode message).length = 8 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length]

theorem encode_length_pos (message : ClearingMemberInitiateOperationConfirmedMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : ClearingMemberInitiateOperationConfirmedMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end ClearingMemberInitiateOperationConfirmedMessage

/-- Flex Clearing Member Initiate Operation Message: 14 bytes -/
structure FlexClearingMemberInitiateOperationMessage where
  subhdr : Subhdr
  partid : BitVec 8
  memberid : BitVec 16
  targetid : BitVec 8
  reqcmseq : BitVec 32
  deriving DecidableEq, Repr

namespace FlexClearingMemberInitiateOperationMessage

def encode (message : FlexClearingMemberInitiateOperationMessage) : List UInt8 :=
  Subhdr.encode message.subhdr
    ++ (encodeUInt 1 message.partid
    ++ (encodeUInt 2 message.memberid
    ++ (encodeUInt 1 message.targetid
    ++ (encodeUInt 4 message.reqcmseq))))

def decode (bytes : List UInt8) : Option (FlexClearingMemberInitiateOperationMessage × List UInt8) := do
  let (subhdr, bytes) ← Subhdr.decode bytes
  let (partid, bytes) ← decodeUInt 1 bytes
  let (memberid, bytes) ← decodeUInt 2 bytes
  let (targetid, bytes) ← decodeUInt 1 bytes
  let (reqcmseq, bytes) ← decodeUInt 4 bytes
  pure ({ subhdr, partid, memberid, targetid, reqcmseq }, bytes)

@[simp] theorem encode_length (message : FlexClearingMemberInitiateOperationMessage) : (encode message).length = 14 := by
  unfold encode
  simp only [List.length_append, Subhdr.encode_length, encodeUInt_length]

theorem encode_length_pos (message : FlexClearingMemberInitiateOperationMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : FlexClearingMemberInitiateOperationMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Subhdr.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end FlexClearingMemberInitiateOperationMessage

/-- Flex Clearing Member Initiate Operation Confirmed Message: 32 bytes -/
structure FlexClearingMemberInitiateOperationConfirmedMessage where
  subhdr : Subhdr
  partid : BitVec 8
  statuscodeUint162 : BitVec 16
  memberid : BitVec 16
  targetid : BitVec 8
  reqcmseq : BitVec 32
  reserved16 : Alpha 16
  deriving DecidableEq, Repr

namespace FlexClearingMemberInitiateOperationConfirmedMessage

def encode (message : FlexClearingMemberInitiateOperationConfirmedMessage) : List UInt8 :=
  Subhdr.encode message.subhdr
    ++ (encodeUInt 1 message.partid
    ++ (encodeUInt 2 message.statuscodeUint162
    ++ (encodeUInt 2 message.memberid
    ++ (encodeUInt 1 message.targetid
    ++ (encodeUInt 4 message.reqcmseq
    ++ (Alpha.encode message.reserved16))))))

def decode (bytes : List UInt8) : Option (FlexClearingMemberInitiateOperationConfirmedMessage × List UInt8) := do
  let (subhdr, bytes) ← Subhdr.decode bytes
  let (partid, bytes) ← decodeUInt 1 bytes
  let (statuscodeUint162, bytes) ← decodeUInt 2 bytes
  let (memberid, bytes) ← decodeUInt 2 bytes
  let (targetid, bytes) ← decodeUInt 1 bytes
  let (reqcmseq, bytes) ← decodeUInt 4 bytes
  let (reserved16, bytes) ← Alpha.decode 16 bytes
  pure ({ subhdr, partid, statuscodeUint162, memberid, targetid, reqcmseq, reserved16 }, bytes)

@[simp] theorem encode_length (message : FlexClearingMemberInitiateOperationConfirmedMessage) : (encode message).length = 32 := by
  unfold encode
  simp only [List.length_append, Subhdr.encode_length, encodeUInt_length, Alpha.encode_length]

theorem encode_length_pos (message : FlexClearingMemberInitiateOperationConfirmedMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : FlexClearingMemberInitiateOperationConfirmedMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Subhdr.decode_encode, some_bind]
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
  rw [Alpha.decode_encode, some_bind]
  rfl

end FlexClearingMemberInitiateOperationConfirmedMessage

/-- Any Payload, selected by Message Type -/
inductive Payload where
  | wakeUpCallMessage (message : WakeUpCallMessage) -- 10
  | wakeUpCallConfirmedMessage (message : WakeUpCallConfirmedMessage) -- 20
  | logonNoticeMessage (message : LogonNoticeMessage) -- 30
  | finalSequentialNumberNotificationForGroupMessage (message : FinalSequentialNumberNotificationForGroupMessage) -- 230
  | requestLogonMessage (message : RequestLogonMessage) -- 40
  | activateApplicationSystemMessage (message : ActivateApplicationSystemMessage) -- 50
  | activateApplicationSystemConfirmedMessage (message : ActivateApplicationSystemConfirmedMessage) -- 60
  | logoutMessage (message : LogoutMessage) -- 70
  | logoutConfirmedMessage (message : LogoutConfirmedMessage) -- 80
  | confirmConnectionMessage (message : ConfirmConnectionMessage) -- 104
  | connectionConfirmedMessage (message : ConnectionConfirmedMessage) -- 105
  | orderStatusReportMessage (message : OrderStatusReportMessage) -- 102
  | orderStatusReportLongFormatMessage (message : OrderStatusReportLongFormatMessage) -- 132
  | executionReportIncludingHeadOfficeAndBranchOfficesMessage (message : ExecutionReportIncludingHeadOfficeAndBranchOfficesMessage) -- 106
  | flexOrderStatusReportMessage (message : FlexOrderStatusReportMessage) -- 202
  | clearingMemberInitiateOperationMessage (message : ClearingMemberInitiateOperationMessage) -- 115
  | clearingMemberInitiateOperationConfirmedMessage (message : ClearingMemberInitiateOperationConfirmedMessage) -- 116
  | flexClearingMemberInitiateOperationMessage (message : FlexClearingMemberInitiateOperationMessage) -- 215
  | flexClearingMemberInitiateOperationConfirmedMessage (message : FlexClearingMemberInitiateOperationConfirmedMessage) -- 216
  deriving DecidableEq, Repr

namespace Payload

/-- The Message Type each message is sent under -/
def tag : Payload → BitVec 8
  | .wakeUpCallMessage _ => 10
  | .wakeUpCallConfirmedMessage _ => 20
  | .logonNoticeMessage _ => 30
  | .finalSequentialNumberNotificationForGroupMessage _ => 230
  | .requestLogonMessage _ => 40
  | .activateApplicationSystemMessage _ => 50
  | .activateApplicationSystemConfirmedMessage _ => 60
  | .logoutMessage _ => 70
  | .logoutConfirmedMessage _ => 80
  | .confirmConnectionMessage _ => 104
  | .connectionConfirmedMessage _ => 105
  | .orderStatusReportMessage _ => 102
  | .orderStatusReportLongFormatMessage _ => 132
  | .executionReportIncludingHeadOfficeAndBranchOfficesMessage _ => 106
  | .flexOrderStatusReportMessage _ => 202
  | .clearingMemberInitiateOperationMessage _ => 115
  | .clearingMemberInitiateOperationConfirmedMessage _ => 116
  | .flexClearingMemberInitiateOperationMessage _ => 215
  | .flexClearingMemberInitiateOperationConfirmedMessage _ => 216

def encode : Payload → List UInt8
  | .wakeUpCallMessage message => WakeUpCallMessage.encode message
  | .wakeUpCallConfirmedMessage message => WakeUpCallConfirmedMessage.encode message
  | .logonNoticeMessage message => LogonNoticeMessage.encode message
  | .finalSequentialNumberNotificationForGroupMessage message => FinalSequentialNumberNotificationForGroupMessage.encode message
  | .requestLogonMessage message => RequestLogonMessage.encode message
  | .activateApplicationSystemMessage message => ActivateApplicationSystemMessage.encode message
  | .activateApplicationSystemConfirmedMessage message => ActivateApplicationSystemConfirmedMessage.encode message
  | .logoutMessage message => LogoutMessage.encode message
  | .logoutConfirmedMessage message => LogoutConfirmedMessage.encode message
  | .confirmConnectionMessage message => ConfirmConnectionMessage.encode message
  | .connectionConfirmedMessage message => ConnectionConfirmedMessage.encode message
  | .orderStatusReportMessage message => OrderStatusReportMessage.encode message
  | .orderStatusReportLongFormatMessage message => OrderStatusReportLongFormatMessage.encode message
  | .executionReportIncludingHeadOfficeAndBranchOfficesMessage message => ExecutionReportIncludingHeadOfficeAndBranchOfficesMessage.encode message
  | .flexOrderStatusReportMessage message => FlexOrderStatusReportMessage.encode message
  | .clearingMemberInitiateOperationMessage message => ClearingMemberInitiateOperationMessage.encode message
  | .clearingMemberInitiateOperationConfirmedMessage message => ClearingMemberInitiateOperationConfirmedMessage.encode message
  | .flexClearingMemberInitiateOperationMessage message => FlexClearingMemberInitiateOperationMessage.encode message
  | .flexClearingMemberInitiateOperationConfirmedMessage message => FlexClearingMemberInitiateOperationConfirmedMessage.encode message

/-- The most bytes any message's encoding can take -/
theorem encode_length_le (message : Payload) : (encode message).length ≤ 5977 := by
  cases message with
  | wakeUpCallMessage inner =>
    simp only [encode, WakeUpCallMessage.encode_length]
    omega
  | wakeUpCallConfirmedMessage inner =>
    simp only [encode, WakeUpCallConfirmedMessage.encode_length]
    omega
  | logonNoticeMessage inner =>
    simp only [encode, LogonNoticeMessage.encode_length]
    omega
  | finalSequentialNumberNotificationForGroupMessage inner =>
    simp only [encode, FinalSequentialNumberNotificationForGroupMessage.encode_length]
    omega
  | requestLogonMessage inner =>
    simp only [encode, RequestLogonMessage.encode_length]
    omega
  | activateApplicationSystemMessage inner =>
    simp only [encode, ActivateApplicationSystemMessage.encode_length]
    omega
  | activateApplicationSystemConfirmedMessage inner =>
    simp only [encode, ActivateApplicationSystemConfirmedMessage.encode_length]
    omega
  | logoutMessage inner =>
    simp only [encode, LogoutMessage.encode_length]
    omega
  | logoutConfirmedMessage inner =>
    simp only [encode, LogoutConfirmedMessage.encode_length]
    omega
  | confirmConnectionMessage inner =>
    simp only [encode, ConfirmConnectionMessage.encode_length]
    omega
  | connectionConfirmedMessage inner =>
    simp only [encode, ConnectionConfirmedMessage.encode_length]
    omega
  | orderStatusReportMessage inner =>
    have bound_inner := OrderStatusReportMessage.encode_length_le inner
    simp only [encode]
    omega
  | orderStatusReportLongFormatMessage inner =>
    have bound_inner := OrderStatusReportLongFormatMessage.encode_length_le inner
    simp only [encode]
    omega
  | executionReportIncludingHeadOfficeAndBranchOfficesMessage inner =>
    have bound_inner := ExecutionReportIncludingHeadOfficeAndBranchOfficesMessage.encode_length_le inner
    simp only [encode]
    omega
  | flexOrderStatusReportMessage inner =>
    have bound_inner := FlexOrderStatusReportMessage.encode_length_le inner
    simp only [encode]
    omega
  | clearingMemberInitiateOperationMessage inner =>
    simp only [encode, ClearingMemberInitiateOperationMessage.encode_length]
    omega
  | clearingMemberInitiateOperationConfirmedMessage inner =>
    simp only [encode, ClearingMemberInitiateOperationConfirmedMessage.encode_length]
    omega
  | flexClearingMemberInitiateOperationMessage inner =>
    simp only [encode, FlexClearingMemberInitiateOperationMessage.encode_length]
    omega
  | flexClearingMemberInitiateOperationConfirmedMessage inner =>
    simp only [encode, FlexClearingMemberInitiateOperationConfirmedMessage.encode_length]
    omega

def decode (tag : BitVec 8) (bytes : List UInt8) : Option (Payload × List UInt8) :=
  if tag = 10 then (WakeUpCallMessage.decode bytes).map fun (message, rest) => (.wakeUpCallMessage message, rest)
  else if tag = 20 then (WakeUpCallConfirmedMessage.decode bytes).map fun (message, rest) => (.wakeUpCallConfirmedMessage message, rest)
  else if tag = 30 then (LogonNoticeMessage.decode bytes).map fun (message, rest) => (.logonNoticeMessage message, rest)
  else if tag = 230 then (FinalSequentialNumberNotificationForGroupMessage.decode bytes).map fun (message, rest) => (.finalSequentialNumberNotificationForGroupMessage message, rest)
  else if tag = 40 then (RequestLogonMessage.decode bytes).map fun (message, rest) => (.requestLogonMessage message, rest)
  else if tag = 50 then (ActivateApplicationSystemMessage.decode bytes).map fun (message, rest) => (.activateApplicationSystemMessage message, rest)
  else if tag = 60 then (ActivateApplicationSystemConfirmedMessage.decode bytes).map fun (message, rest) => (.activateApplicationSystemConfirmedMessage message, rest)
  else if tag = 70 then (LogoutMessage.decode bytes).map fun (message, rest) => (.logoutMessage message, rest)
  else if tag = 80 then (LogoutConfirmedMessage.decode bytes).map fun (message, rest) => (.logoutConfirmedMessage message, rest)
  else if tag = 104 then (ConfirmConnectionMessage.decode bytes).map fun (message, rest) => (.confirmConnectionMessage message, rest)
  else if tag = 105 then (ConnectionConfirmedMessage.decode bytes).map fun (message, rest) => (.connectionConfirmedMessage message, rest)
  else if tag = 102 then (OrderStatusReportMessage.decode bytes).map fun (message, rest) => (.orderStatusReportMessage message, rest)
  else if tag = 132 then (OrderStatusReportLongFormatMessage.decode bytes).map fun (message, rest) => (.orderStatusReportLongFormatMessage message, rest)
  else if tag = 106 then (ExecutionReportIncludingHeadOfficeAndBranchOfficesMessage.decode bytes).map fun (message, rest) => (.executionReportIncludingHeadOfficeAndBranchOfficesMessage message, rest)
  else if tag = 202 then (FlexOrderStatusReportMessage.decode bytes).map fun (message, rest) => (.flexOrderStatusReportMessage message, rest)
  else if tag = 115 then (ClearingMemberInitiateOperationMessage.decode bytes).map fun (message, rest) => (.clearingMemberInitiateOperationMessage message, rest)
  else if tag = 116 then (ClearingMemberInitiateOperationConfirmedMessage.decode bytes).map fun (message, rest) => (.clearingMemberInitiateOperationConfirmedMessage message, rest)
  else if tag = 215 then (FlexClearingMemberInitiateOperationMessage.decode bytes).map fun (message, rest) => (.flexClearingMemberInitiateOperationMessage message, rest)
  else if tag = 216 then (FlexClearingMemberInitiateOperationConfirmedMessage.decode bytes).map fun (message, rest) => (.flexClearingMemberInitiateOperationConfirmedMessage message, rest)
  else none

@[simp] theorem decode_encode (message : Payload) (rest : List UInt8) :
    decode (tag message) (encode message ++ rest) = some (message, rest) := by
  cases message <;> simp [decode, encode, tag]

end Payload

/-- Message Tail: 1 bytes -/
structure MessageTail where
  checkSum : BitVec 8
  deriving DecidableEq, Repr

namespace MessageTail

def encode (message : MessageTail) : List UInt8 :=
  encodeUInt 1 message.checkSum

def decode (bytes : List UInt8) : Option (MessageTail × List UInt8) := do
  let (checkSum, bytes) ← decodeUInt 1 bytes
  pure ({ checkSum }, bytes)

@[simp] theorem encode_length (message : MessageTail) : (encode message).length = 1 := by
  unfold encode
  simp only [encodeUInt_length]

theorem encode_length_pos (message : MessageTail) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : MessageTail) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end MessageTail

/-- Tmp Message -/
structure TmpMessage where
  msgLength : BitVec 16
  msgSeqNum : BitVec 32
  headerTime : HeaderTime
  fcmid : BitVec 16
  sessionid : BitVec 16
  payload : Payload
  messageTail : MessageTail
  deriving DecidableEq, Repr

namespace TmpMessage

def encode (message : TmpMessage) : List UInt8 :=
  encodeUInt 2 message.msgLength
    ++ (encodeUInt 4 message.msgSeqNum
    ++ (HeaderTime.encode message.headerTime
    ++ (encodeUInt 1 (Payload.tag message.payload)
    ++ (encodeUInt 2 message.fcmid
    ++ (encodeUInt 2 message.sessionid
    ++ (Payload.encode message.payload
    ++ (MessageTail.encode message.messageTail)))))))

def decode (bytes : List UInt8) : Option (TmpMessage × List UInt8) := do
  let (msgLength, bytes) ← decodeUInt 2 bytes
  let (msgSeqNum, bytes) ← decodeUInt 4 bytes
  let (headerTime, bytes) ← HeaderTime.decode bytes
  let (messageType, bytes) ← decodeUInt 1 bytes
  let (fcmid, bytes) ← decodeUInt 2 bytes
  let (sessionid, bytes) ← decodeUInt 2 bytes
  let (payload, bytes) ← Payload.decode messageType bytes
  let (messageTail, bytes) ← MessageTail.decode bytes
  pure ({ msgLength, msgSeqNum, headerTime, fcmid, sessionid, payload, messageTail }, bytes)

theorem encode_length_pos (message : TmpMessage) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUInt_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : TmpMessage) : (encode message).length ≤ 5995 := by
  unfold encode
  cases message.payload with
  | wakeUpCallMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, HeaderTime.encode_length, MessageTail.encode_length, WakeUpCallMessage.encode_length]
    omega
  | wakeUpCallConfirmedMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, HeaderTime.encode_length, MessageTail.encode_length, WakeUpCallConfirmedMessage.encode_length]
    omega
  | logonNoticeMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, HeaderTime.encode_length, MessageTail.encode_length, LogonNoticeMessage.encode_length]
    omega
  | finalSequentialNumberNotificationForGroupMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, HeaderTime.encode_length, MessageTail.encode_length, FinalSequentialNumberNotificationForGroupMessage.encode_length]
    omega
  | requestLogonMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, HeaderTime.encode_length, MessageTail.encode_length, RequestLogonMessage.encode_length]
    omega
  | activateApplicationSystemMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, HeaderTime.encode_length, MessageTail.encode_length, ActivateApplicationSystemMessage.encode_length]
    omega
  | activateApplicationSystemConfirmedMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, HeaderTime.encode_length, MessageTail.encode_length, ActivateApplicationSystemConfirmedMessage.encode_length]
    omega
  | logoutMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, HeaderTime.encode_length, MessageTail.encode_length, LogoutMessage.encode_length]
    omega
  | logoutConfirmedMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, HeaderTime.encode_length, MessageTail.encode_length, LogoutConfirmedMessage.encode_length]
    omega
  | confirmConnectionMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, HeaderTime.encode_length, MessageTail.encode_length, ConfirmConnectionMessage.encode_length]
    omega
  | connectionConfirmedMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, HeaderTime.encode_length, MessageTail.encode_length, ConnectionConfirmedMessage.encode_length]
    omega
  | orderStatusReportMessage inner =>
    have bound_inner := OrderStatusReportMessage.encode_length_le inner
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, HeaderTime.encode_length, MessageTail.encode_length]
    omega
  | orderStatusReportLongFormatMessage inner =>
    have bound_inner := OrderStatusReportLongFormatMessage.encode_length_le inner
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, HeaderTime.encode_length, MessageTail.encode_length]
    omega
  | executionReportIncludingHeadOfficeAndBranchOfficesMessage inner =>
    have bound_inner := ExecutionReportIncludingHeadOfficeAndBranchOfficesMessage.encode_length_le inner
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, HeaderTime.encode_length, MessageTail.encode_length]
    omega
  | flexOrderStatusReportMessage inner =>
    have bound_inner := FlexOrderStatusReportMessage.encode_length_le inner
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, HeaderTime.encode_length, MessageTail.encode_length]
    omega
  | clearingMemberInitiateOperationMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, HeaderTime.encode_length, MessageTail.encode_length, ClearingMemberInitiateOperationMessage.encode_length]
    omega
  | clearingMemberInitiateOperationConfirmedMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, HeaderTime.encode_length, MessageTail.encode_length, ClearingMemberInitiateOperationConfirmedMessage.encode_length]
    omega
  | flexClearingMemberInitiateOperationMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, HeaderTime.encode_length, MessageTail.encode_length, FlexClearingMemberInitiateOperationMessage.encode_length]
    omega
  | flexClearingMemberInitiateOperationConfirmedMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUInt_length, HeaderTime.encode_length, MessageTail.encode_length, FlexClearingMemberInitiateOperationConfirmedMessage.encode_length]
    omega

@[simp] theorem decode_encode (message : TmpMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, HeaderTime.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Payload.decode_encode, some_bind]
  dsimp only
  rw [MessageTail.decode_encode, some_bind]
  rfl

end TmpMessage

end Omi.TaifexTaifexderivativesClearingmemberTmpV2187
