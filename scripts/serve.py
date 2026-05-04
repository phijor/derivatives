from http.server import SimpleHTTPRequestHandler, HTTPServer
from os import chdir, getenv
import socketserver


class NoCacheHandler(SimpleHTTPRequestHandler):
    def end_headers(self):
        self.send_header(
            "Cache-Control", "no-store, no-cache, must-revalidate, max-age=0"
        )
        self.send_header("Pragma", "no-cache")
        self.send_header("Expires", "0")
        super().end_headers()


if __name__ == "__main__":
    if dir := getenv("AGDA_SITE_DIR"):
        print(f"Serving files from '{dir}'")
        chdir(dir)

    PORT = 8001
    with socketserver.TCPServer(("", PORT), NoCacheHandler) as httpd:
        print(f"Serving site at 'http://127.0.0.1:{PORT}'")
        httpd.serve_forever()
