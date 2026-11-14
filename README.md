# prime-certificates

決定的な素数証明の台帳。ブラウザの「証素」がこの公開リポジトリを読み、証明書 JSON は因数探索なしで再検証する。

## ファイル

- `candidates.txt` — 1行に1つの整数式。証素の入力にそのまま載る。
- `certificates/` — 証明 JSON。
- `verify.mjs` — 証明書だけを再実行する検証器。証明の探索はしない。

```
node verify.mjs certificates/mersenne-2-89-minus-1.json
```

`prime` と十進数が出れば証明は通っている。

## 何が証明になるか

- `factor` — 明示的な因数。合成数。
- `mr-composite` / `fermat` — 合同式ひとつで合成数。
- `mr` — n が表の限界未満で、その行の証人をすべて通る。限界は 3317044064679887385961981 未満まで。底を勝手に減らした証明書は拒否する。
- `ll` — 指数 p の素数証明つき Lucas–Lehmer。2^p−1。
- `pocklington` — n−1 の因数 M について、各 q^e で a^(n−1) ≡ 1 かつ gcd(a^((n−1)/q^e)−1, n) = 1。M^2 > n なら Pocklington。立方根を超え平方根以下で判別式が非平方なら Brillhart–Lehmer–Selfridge。

確率的素数（PRP）だけのデータは置かない。閉じないものは未証明として扱う。
