1. Install elan, codex, git, python

2. `git clone https://github.com/yuanyi-350/TongWen_script && mv TongWen_script/* . && rm -rf TongWen_script/`

3. Codex Settings

   (1) Grant Codex permissions and trust this directory.

   (2) Install `lean-lsp-mcp` by copy `.codex/config.toml`

   (3) Test by `/mcp` in codex.

4. Lean Settings

   (1) Use prompt in [VersionSync_PROMPT.md](VersionSync_PROMPT.md) to update `lean-toolchain`, `lake-manifest.json` and `lakefile.toml` ,

   (2) Run `ln -s ~/.global_lake .lake` in terminal.

   (3) Test the setup by running `lake exe cache get` and `lake build Mathlib`.

5. Git Settings

   (1) Fork the repo and change `git remote -v`

   (2) Test `git push`

6. setup `WORKERS` environment variable and run `python3 pipeline.py --dir Optlib`
