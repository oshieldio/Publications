# Snapper Attack Investigation Report — Final

---

## Overview

This report presents the findings of an on-chain investigation into the Snapper DEX and Fomo protocol hack, which drained liquidity pools through a malicious program upgrade. After an extended investigation involving on-chain tracing, OSINT analysis, direct collaboration with the affected team, and communication with the IC3 (Internet Crime Complaint Center), we have reached a definitive conclusion attributing the attack to a developer operating under the alias **"Tony"** (cuiguo23@gmail.com).

The prior Snapper Analysis publication (available in this repository) documented the attack mechanics and flagged anomalies in the funding chain that were consistent with an inside actor — but at that stage the evidence was circumstantial and no individual could be named. This report closes that gap. The findings presented here have been independently reviewed by third-party researchers and community members prior to publication.

---

## Prior Investigation — Red Flags, Not Yet Conclusive

Our earlier Snapper Analysis (available in this repository) uncovered an intricate, multi-layered fund movement network — six-hop funding chains, purpose-built relay accounts with minimal transaction histories, a token-based laundering scheme converting billions of SOSA tokens into approximately 350 SOL across six operational wallets, and exchange-based exits through KuCoin and MEXC. The level of preparation was far beyond what an opportunistic external attacker would invest, pointing strongly to someone who had prior experience infiltrating or working within developer teams and exploiting that access for financial gain. No individual could be conclusively identified from that analysis alone, but the operational sophistication was consistent with a pattern of deliberate, insider-enabled attacks rather than a one-off exploit.

Initial attribution was further complicated when the team server was accessed from a **Polish IP address** at the time the upgrade authority keypair was extracted. This appeared to implicate another developer on the team based in Poland, and the team initially accepted that framing. Tony had deliberately routed his connection through a Polish IP in an attempt to frame his colleague — a deception that held until the September 2024 slip unraveled it.

---

## The Decisive Connection — September 2024

The decisive breakthrough came in **September 2024**, when one of Tony's known salary addresses made a direct deposit into a MEXC exchange address we had been actively monitoring as part of the attack fund flow.

Specifically, wallet (5TLm...iNEw) — an address Tony had shared with team members in Telegram to receive his monthly salary payments — sent funds directly to MEXC deposit address (6WqU...KYVS) in transaction [5E1f...VDna](https://solscan.io/tx/5E1fDk94D9dfNQAyhmHrLahrauMoRcLG8WowWkq8Dq7pxhdoD36Xru9DW3JUvteRZBqZrY5HQbc72einYFwFVDna).

We cross-referenced the sending address against the team's Telegram records. The match was exact. This single transaction linked Tony's personal payroll wallet to the same MEXC destination that received the attack proceeds.

Combined with the broader on-chain evidence and context provided by the team, this established conclusive attribution.

---

## Key Findings

1. **Tony abused server access to steal the upgrade authority key.** He was not assigned update authority on either program. Rather, he had access to the server where the upgrade authority keypair was stored, and used it to execute the malicious upgrade without authorization.
2. **Attack proceeds flowed to Tony's MEXC accounts.** The drainer address and Tony's own program authority wallets sent funds directly to two MEXC deposit addresses controlled by the same entity.
3. **Tony's salary wallet sent funds to the same MEXC destination.** In September 2024, a payroll address Tony shared in Telegram sent funds to one of the monitored MEXC addresses, creating an irrefutable link between his personal accounts and the attack proceeds.
4. **OSINT reveals a network of fabricated identities.** Tony operated multiple GitHub accounts (`evgpan`, `devsky83`, and others) with shared commit emails and cross-following patterns consistent with a coordinated fake-developer operation, potentially DPRK-affiliated.
5. **Pattern of infiltrating Solana projects.** The same identity network was previously linked to Cropper Finance and to the SOSA token operation documented in our prior report. Beyond these confirmed connections, Tony's GitHub account network shows contributions to and associations with a number of other projects that we cannot fully attribute with certainty — but the breadth of that activity suggests this was not his first attempt at embedding himself within a team with the intent to exploit it.

---

## On-Chain Evidence

### Attack Addresses


| Role                            | Address       |
| ------------------------------- | ------------- |
| Original Update Authority       | G882...bs8A |
| Tony — Snapper Update Authority | HgDp...EGRm |
| Tony — Fomo Update Authority    | DLku...BhxL |
| Primary Drainer Address         | DpVQ...r3P4 |


Full addresses for independent verification:


| Role                            | Full Address                                   |
| ------------------------------- | ---------------------------------------------- |
| Original Update Authority       | G882tNd4ihoSMtsP7Ro21j4XkGmED4KLjTCdpj2sbs8A |
| Tony — Snapper Update Authority | HgDp1vxXwNGQyeP8RxP9Af26pyeW3cTG98gNKytBEGRm |
| Tony — Fomo Update Authority    | DLkut5kcEpBocjyTRzrTomhjrKC4nBEMWAnwLC4yBhxL |
| Primary Drainer Address         | DpVQL14NUhoVgTSjunBjG365DhprozFgYu8hDznLr3P4 |


### Tony's Known Salary Addresses (sourced from team Telegram records)


| Label              | Short         | Full Address                                   |
| ------------------ | ------------- | ---------------------------------------------- |
| Address 1          | 5TLm...iNEw | 5TLmCwUWvkd4tc87VHRVUoDptyL2mmVL5jMo9N2RiNEw |
| Address 2          | 2HtV...RuZC | 2HtVfgx88YA2oru6tTwmjT28aLxApWXKmw8s436hRuZC |
| Address 3 (Weekly) | 9Tg6...PWpG | 9Tg6gfLATpis3mYBM64PP4nCjZUXRKaycRuiryZAPWpG |
| Address 4          | JD45...T4XB | JD451MPchwvVVnWVjGBdQkMR5VP2FJkogW42bejJT4XB |


### Confirmed MEXC Deposit Addresses (Attack Destination)


| Label  | Short         | Full Address                                   |
| ------ | ------------- | ---------------------------------------------- |
| MEXC 1 | 6WqU...KYVS | 6WqUhpD4RHi3Nwv6btT7pxCWL9QQrTbnCg3KBRaJKYVS |
| MEXC 2 | Cbto...ocYT | CbtoFFNDanWKnTJnv3TDSNWZG7tFAQmyNew23yzYocYT |


The wallet (BRmf...8iSx) deposited into both MEXC addresses, adding additional support to the fact that they belong to the same operator:

| From | To | Transaction |
|---|---|---|
| BRmf...8iSx | MEXC 1 (6WqU...KYVS) | [4osh...hNvz](https://solscan.io/tx/4oshwmogiGNXjMdocsTTESkA1nerYVscMyKNQAqWuGJq6CS4WAs65fzfGxDv36oiuZ2sqj4CeNmDtoUCuzAmhNvz) |
| BRmf...8iSx | MEXC 2 (Cbto...ocYT) | [4m81...CaQJ](https://solscan.io/tx/4m81SJUu6pqgZzLrCBkTd4EVKADrHdMUzsGg7yGL6fJEXNCFq4sq7FE6TWnDghxopVRsMXvQvbzehS53ANiHCaQJ) |


### Attack Fund Movement — Authority Wallets to MEXC


| From                                 | To                     | Transaction                                                                                                                  |
| ------------------------------------ | ---------------------- | ---------------------------------------------------------------------------------------------------------------------------- |
| Drainer (DpVQ...r3P4) | MEXC 1 (6WqU...KYVS) | [5vKr...RHD](https://solscan.io/tx/5vKrseKzbyLnY6qEXwTbZUywVk4DVawne6Gy53Wmn48cHk9nEW8LgTsu5Jr4jTs4fcWyFgV2C4ryrDyayK1M9RHD) |
| Tony Snapper Authority (HgDp...EGRm) | MEXC 2 (Cbto...ocYT) | [4kKq...iKk](https://solscan.io/tx/4kKqR3VaM1upfGMqNf9G5m2akvr5WgJ2QPhmWWULEcPB7j4RLaxzscFCnf7Ze2JEHW7Dy6bBaizHgpGYmsFdqiKk) |
| Tony Fomo Authority (DLku...BhxL) | MEXC 1 (6WqU...KYVS) | [42SG...x7K](https://solscan.io/tx/42SGtrEy2BdooCTfQ1ZAW4aVdLhzyjzwgcMjKGZ4CQAHU9veJhg9HU1nwYKycgjG7tVdqVLj5AapQc7cFAiFgx7K) |


### Salary Address Fund Movement to MEXC (The Decisive Connection — September 2024)

All four of Tony's known salary addresses sent funds to the same MEXC destinations as the attack proceeds:


| From (Salary Address)   | To                     | Transaction                                                                                                                   |
| ----------------------- | ---------------------- | ----------------------------------------------------------------------------------------------------------------------------- |
| Address 4 (JD45...T4XB) | MEXC 1 (6WqU...KYVS) | [2Tj2...oR84](https://solscan.io/tx/2Tj2WAQopxJLTdRCu5H9KkpcCeDSYtKT9KCNFNtTpZAZbLQHcx5iSsA5uXBjJy5w7fJByWBcPc5mfxWcocE1oR84) |
| Address 4 (JD45...T4XB) | MEXC 1 (6WqU...KYVS) | [5z5f...YP9f](https://solscan.io/tx/5z5fop1Zn975Xm9vSENEbQEjX4gQu7YjNKbm24aPmK4jkLAFRbyUw7jhHgpb7ZU9sq8nyFvck5Zmz8wPYwP7YP9f) |
| Address 4 (JD45...T4XB) | MEXC 1 (6WqU...KYVS) | [4RFd...ZKjG](https://solscan.io/tx/4RFdQJBnpZQ7ASQerNyBRfQFZrgdRBjUgZ5R1uUZMRwe3ebML7J7U7XmuHnLCDuxht45SPDPksY36detN5Y2ZKjG) |
| Address 2 (2HtV...RuZC) | MEXC 2 (Cbto...ocYT) | [2Mcg...Yi2Z](https://solscan.io/tx/2McgHrJkzKscJVzhvdqPXT7V8A69TbRNFPPrnWpWQrxE9STRpfkWRRezvEFaxdjMzteH7wf589hToFnkAViYYi2Z) |
| Address 1 (5TLm...iNEw) | MEXC 1 (6WqU...KYVS) | [5E1f...VDna](https://solscan.io/tx/5E1fDk94D9dfNQAyhmHrLahrauMoRcLG8WowWkq8Dq7pxhdoD36Xru9DW3JUvteRZBqZrY5HQbc72einYFwFVDna) |
| Address 3 (9Tg6...PWpG) | MEXC 1 (6WqU...KYVS) | [2v1G...VU9X](https://solscan.io/tx/2v1GuNJeETYhxTL5rDLacjiLU6ULzgtX3cHW4bpTTkNcb25SQKVcRFjBgoEpGNgCQp2mW99ftrpjjC7vtTNnVU9X) |
| Address 3 (9Tg6...PWpG) | MEXC 1 (6WqU...KYVS) | [4h7G...C8Jd](https://solscan.io/tx/4h7GDp1CVnfjswhkUNaVQ46SXBnN6hRP5thP8zTrDxgrakYxncvTyDP1E2mSUKPG1zGjrxftzaJFWskzCgaxC8Jd) |
| Address 3 (9Tg6...PWpG) | MEXC 1 (6WqU...KYVS) | [2gQG...uFPE](https://solscan.io/tx/2gQGAHQhBt3PSuGcuxEZsPbh8AMXv5fPwEgC9tT14T58wzrowiuoGzqoGjzZpwdcnBEyf4yedmscxWvZCZZwuFPE) |


---

## OSINT — Identity Network

Analysis of Tony's GitHub activity and email footprint reveals a network of interconnected accounts consistent with a coordinated multi-persona operation.

### GitHub Accounts


| Account      | Link                                                               |
| ------------ | ------------------------------------------------------------------ |
| evgpan       | [https://github.com/evgpan](https://github.com/evgpan)             |
| devsky83     | [https://github.com/devsky83](https://github.com/devsky83)         |
| martin920105 | [https://github.com/martin920105](https://github.com/martin920105) |
| soldev3639   | [https://github.com/soldev3639](https://github.com/soldev3639)     |
| alinkon0207  | [https://github.com/alinkon0207](https://github.com/alinkon0207)   |
| ilesoviy     | [https://github.com/ilesoviy](https://github.com/ilesoviy)         |


All accounts follow each other in a circular pattern.

**evgpan and devsky83 are the same person:** The `evgpan` repository `img2img` contains commits by `jackvich` (evgenpan228@gmail.com); the `devsky83` repository `next-cms-ghost` contains commits by `devsky83` (jackvich2022@gmail.com). The shared `jackvich` handle across both email addresses confirms a single operator. GitHub's own verified names field lists both `jackvich` and `devsky83` for account ID `143729467`.

**Connection to Cropper Finance:** The repository [CropperFinance/cropper_instructions](https://github.com/CropperFinance/cropper_instructions) contains commits by `SolanaEngineer` (topstack2021a@gmail.com). Tony was a Trello member of the same Cropper Finance workspace under the username `tony_cropper`.

*To independently verify account linkages: clone each repository and run `git log` to inspect embedded commit author names and email addresses.*

### Email OSINT

#### cuiguo23@gmail.com — Tony (Primary)

The OSINT search shows this email active across 398 sources with 9 hits. It surfaces under the username `TONY_CROPPER` on Trello, where the account was last seen on 8 July 2024 and the profile is tied to the Cropper Finance workspace — directly linking this identity to that project. A Microsoft account registered under the name "Tony Guo" with a US location was created on 30 June 2025, a notably recent date suggesting a freshly constructed identity. A Google account under the same email was also found. The search further shows active accounts on Calendly, Fotor, Asana, and HackerRank.

---

#### jackvich2022@gmail.com — devsky83 / "Jack P."

The OSINT search shows this email across 416 sources with 12 hits, operating under the username `DEVSKY83`. The search reveals an Upwork profile under the name "Jack P." located in Toronto, Canada, with a bio listing Rust, TypeScript, and Python — consistent with the developer profile used to secure employment on Solana teams. The listed location is Toronto but the timezone recorded is UTC-08:00 Pacific Time, not the UTC-05:00 that Toronto actually uses, indicating a fabricated location. The GitHub account linked to this email was recently active as of May 2026 and shows verified names of both `jackvich` and `devsky83` on the same account, providing platform-level confirmation that these are the same operator.

---

#### topstack2021a@gmail.com — "Hongbo Li" / SolanaEngineer

The OSINT search shows this email across 386 sources with 7 hits, surfacing under the name "Hongbo Li" with a location in Klintsy, Bryansk, Russia. A LinkedIn profile was found under the username `hongbo-li-650674217` with a bio describing the account as "Solana Lead Engineer" — matching the `SolanaEngineer` commit identity found in the Cropper Finance repository. A Notion account under the same name was also found. Despite the different name and Russian location, this is the same email used to commit code in a project where cuiguo23@gmail.com was simultaneously a member, pointing to a single operator running multiple personas.

---

#### evgenpan228@gmail.com — evgpan / jackvich

The OSINT search shows this email across 390 sources with 5 hits. Only a Google account and an associated Google Maps account were found, last seen 12 October 2023. This appears to be the oldest and most dormant identity in the network, likely a precursor to the more active personas developed under the other emails.

---

## IC3 Complaint and Outcome

Following the September 2024 confirmation, we assisted the affected team in filing a complaint with the **IC3 (Internet Crime Complaint Center)**. The complaint documented the on-chain fund flows, the salary address connection, Tony's identity network, and the broader pattern of fake developer personas.

After an extended period of communication, the investigation was unable to proceed further. The primary reasons cited were the elapsed time since the incident, the scale of the theft relative to the jurisdictional threshold required for active pursuit, and — critically — the credible possibility that Tony is a **DPRK-affiliated IT worker**. The multi-identity structure, the Russian-located personas, the fabricated Western profiles used to secure employment on Solana projects, and the pattern of moving funds to centralized exchanges are all consistent with documented DPRK IT worker tradecraft.

When state-level actors are involved, law enforcement avenues available to private citizens and small teams reach their limits quickly.

---

## Conclusion

We are releasing this report publicly for the following reasons:

1. **Transparency to the community.** Users and protocols who lost funds deserve to know who was responsible and how the attribution was established.
2. **Warning to other projects.** The identity network documented here — fake GitHub accounts, multi-email personas, Upwork profiles with fabricated locations, and a pattern of targeting Solana projects — may still be active. Other teams should vet contributors against these indicators.
3. **Record for future enforcement.** Even where current legal channels are exhausted, a documented and timestamped public record may support future action if circumstances change or additional victims emerge.

The evidence is conclusive: **the developer operating under the alias "Tony" is responsible for the Snapper and Fomo protocol hack.** The connection was established through a direct on-chain link between his salary-receiving wallet — verified against Telegram payment records — and the MEXC exchange addresses that received the stolen funds.