# Inspecting results

## g2html
1. First time run: `make jar`.
2. Run Goblint with additional `--html` argument.
3. Run in `./result` directory: `python3 -m http.server 8080` or `npx http-server`.
4. Inspect results at <http://localhost:8080/index.xml>.

Modern browsers' security settings forbid some file access which is necessary for g2html to work, hence the need for serving the results via Python's `http.server` (or similar).
