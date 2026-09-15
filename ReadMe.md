# Omi Lean Protocols

Omi [Lean](https://lean-lang.org/ "The Lean theorem prover and programming language") protocols describe common binary exchange protocols as Lean 4 definitions that carry their own proofs: for every message, decoding what was encoded gives the message back and the encoding is exactly as wide as the specification says; the dispatch on the message type selects the message that was written; and where the model states a length prefix or a message count, the framing decodes back as well.


[![Lean](https://github.com/Open-Markets-Initiative/Open-Markets-Initiative/blob/main/About/Images/Lean.png)](https://lean-lang.org/)

These definitions are checked with the Lean toolchain: [lake](https://lean-lang.org/doc/reference/latest/ "The Lean language reference")
## Usage

Each .lean file is a self contained module for one protocol version: a structure per message, an inductive per coded field, a sum type dispatching on the message type, and the theorems relating each decoder to its encoder. The shared `Omi/Wire.lean` holds the field kinds (big and little endian integers, fixed width text, counted repetition) and their lemmas. Check every proof with lake:

```
lake build
```
A definition is used as an ordinary Lean library: `decode` reads a `List UInt8` and returns the message with the bytes that follow, `encode` writes one, and the theorems are available to anything built on top.

For toolchain information: [Lean Toolchain](https://lean-lang.org/install/ "Installing Lean")
## Development

Updates are greatly appreciated; however, this entire repository is source generated...including the words you are reading right now. If you wish to suggest definition updates, the recommended process is to create an issue with changes and explanation.  Time permitting, we will update the models and regenerate.

| Protocol Count | Generated Lines |
| --- | --- |
| 12 | 16891 |

## Testing

[![Build](https://github.com/Open-Markets-Initiative/omi-lean-protocols/actions/workflows/build.yml/badge.svg)](https://github.com/Open-Markets-Initiative/omi-lean-protocols/actions/workflows/build.yml)

The build checks every proof. The tests under `tests/` decode captured packets from [omi-data-packets](https://github.com/Open-Markets-Initiative/omi-data-packets "Omi Data Packets") and require each to be consumed exactly; each is a theorem decided at build time, so a failing test fails the build.

Please report any parsing errors as an [issue](https://github.com/Open-Markets-Initiative/omi-lean-protocols/issues "Omi Lean Issues").  Include a small note on the protocol and version, and a minimal capture demonstrating the problem. Also consider including a link or pdf specification documenting the correct behavior.

## Open Markets Initiative

The Open Markets Initiative (Omi) is a group of technologists dedicated to enhancing the stability of electronic financial markets using modern development methods.

Other generated code can be found at [Omi Projects](https://github.com/Open-Markets-Initiative/Directory/tree/main/Projects "Open Markets Initiative Projects"); for Omi rules and regulations, see [Omi Directory](https://github.com/Open-Markets-Initiative/Directory "Open Markets Initiative Directory").
## Organizations

> [Iex][Iex.Directory] · [Nasdaq][Nasdaq.Directory]

## Exchanges

> [IexEquities][IexEquities.Exchange] · [NsmEquities][NsmEquities.Exchange] · [NtxEquities][NtxEquities.Exchange] · [PsxEquities][PsxEquities.Exchange]

## Related Definitions

The Open Markets Initiative provides protocol definitions in several formats:

- [Kaitai Struct Definitions][Kaitai.Definitions.Repository] — cross language binary parsers with the kaitai struct compiler
- [DFDL Definitions][Dfdl.Definitions.Repository] — declarative DFDL schemas for cross language parsing
- [P4 Definitions][P4.Definitions.Repository] — P4 programs for software and hardware data planes
- [Spicy Definitions][Spicy.Definitions.Repository] — declarative Spicy grammars for the spicy toolchain and the zeek network security monitor
- [FIX Dictionaries][Fix.Dictionaries.Repository] — QuickFIX format xml data dictionaries, one per FIX version
- [Xml Specifications][Xml.Specifications.Repository] — the exchange protocol specification xmls, matching the original files
## Disclaimer

Any similarities between existing people, places and/or protocols is purely incidental.

Enjoy.

[Omi Projects]: https://github.com/Open-Markets-Initiative/Directory/tree/main/Projects "Open Markets Initiative Projects"
[Omi Rules and Regulations]: https://github.com/Open-Markets-Initiative/Directory/tree/main/License "Open Markets Initiative Rules and Regulations"

[Omi.Glossary.Testing]: https://github.com/Open-Markets-Initiative/Open-Markets-Initiative/blob/main/Glossary/Testing.md "Protocol Testing Status"
[Omi.Glossary.Testing.Verified]: https://github.com/Open-Markets-Initiative/Open-Markets-Initiative/blob/main/Glossary/Testing.md "Testing Status: Protocol has been tested on live data"
[Omi.Glossary.Testing.Incomplete]: https://github.com/Open-Markets-Initiative/Open-Markets-Initiative/blob/main/Glossary/Testing.md "Testing Status: Protocol has been tested on live data but contains known issues"
[Omi.Glossary.Testing.Beta]: https://github.com/Open-Markets-Initiative/Open-Markets-Initiative/blob/main/Glossary/Testing.md "Testing Status: Protocol has not been tested and structure is speculative"
[Omi.Glossary.Testing.Untested]: https://github.com/Open-Markets-Initiative/Open-Markets-Initiative/blob/main/Glossary/Testing.md "Testing Status: Protocol has not been tested on live data"
[Omi.Glossary.Testing.Unavailable]: https://github.com/Open-Markets-Initiative/Open-Markets-Initiative/blob/main/Glossary/Testing.md "Testing Status: Protocol does not state a testing status"
[Omi.Encoding.Definitions]: https://github.com/Open-Markets-Initiative/Open-Markets-Initiative/blob/main/Protocols/ReadMe.md "Encoding Directory"

[Omi.Encoding.IexTp]: https://github.com/Open-Markets-Initiative/Directory/blob/main/Protocols/IexTp.md "IexTp Encoding"
[Omi.Encoding.Itch]: https://github.com/Open-Markets-Initiative/Directory/blob/main/Protocols/Itch.md "Itch Encoding"

[Iex.IexEquities.Tops]: https://github.com/Open-Markets-Initiative/Open-Markets-Initiative/blob/main/Organizations/Iex/Protocols/IexEquities/Tops.md "Top Of Book"
[Iex.IexEquities.Deep]: https://github.com/Open-Markets-Initiative/Open-Markets-Initiative/blob/main/Organizations/Iex/Protocols/IexEquities/Deep.md "Depth Of Book"
[Iex.IexEquities.DeepPlus]: https://github.com/Open-Markets-Initiative/Open-Markets-Initiative/blob/main/Organizations/Iex/Protocols/IexEquities/DeepPlus.md "DeepPlus"
[Nasdaq.NsmEquities.TotalView]: https://github.com/Open-Markets-Initiative/Open-Markets-Initiative/blob/main/Organizations/Nasdaq/Protocols/NsmEquities/TotalView.md "TotalView Itch"
[Nasdaq.NtxEquities.TotalView]: https://github.com/Open-Markets-Initiative/Open-Markets-Initiative/blob/main/Organizations/Nasdaq/Protocols/NtxEquities/TotalView.md "TX TotalView Itch"
[Nasdaq.PsxEquities.TotalView]: https://github.com/Open-Markets-Initiative/Open-Markets-Initiative/blob/main/Organizations/Nasdaq/Protocols/PsxEquities/TotalView.md "TotalView Itch"

[Iex.Directory]: https://github.com/Open-Markets-Initiative/omi-lean-protocols/tree/main/iex "Investors Exchange"
[Nasdaq.Directory]: https://github.com/Open-Markets-Initiative/omi-lean-protocols/tree/main/nasdaq "National Association of Securities Dealers Automated Quotations (Nasdaq)"

[IexEquities.Exchange]: https://github.com/Open-Markets-Initiative/omi-lean-protocols/tree/main/iex "IEX Equities"
[NsmEquities.Exchange]: https://github.com/Open-Markets-Initiative/omi-lean-protocols/tree/main/nasdaq/nsmequities "Nasdaq Stock Market"
[NtxEquities.Exchange]: https://github.com/Open-Markets-Initiative/omi-lean-protocols/tree/main/nasdaq/ntxequities "Nasdaq Texas"
[PsxEquities.Exchange]: https://github.com/Open-Markets-Initiative/omi-lean-protocols/tree/main/nasdaq/psxequities "Nasdaq PSX"

[Kaitai.Definitions.Repository]: https://github.com/Open-Markets-Initiative/omi-kaitai-struct-definitions "Omi Kaitai Struct Definitions"
[Dfdl.Definitions.Repository]: https://github.com/Open-Markets-Initiative/omi-dfdl-definitions "Omi DFDL Definitions"
[P4.Definitions.Repository]: https://github.com/Open-Markets-Initiative/omi-p4-definitions "Omi P4 Definitions"
[Spicy.Definitions.Repository]: https://github.com/Open-Markets-Initiative/omi-spicy-definitions "Omi Spicy Definitions"
[Fix.Dictionaries.Repository]: https://github.com/Open-Markets-Initiative/omi-fix-dictionaries "Omi FIX Dictionaries"
[Xml.Specifications.Repository]: https://github.com/Open-Markets-Initiative/omi-xml-specifications "Omi Xml Specifications"
