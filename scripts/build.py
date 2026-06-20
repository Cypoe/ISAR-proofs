import subprocess
import sys

def main():
    print("Building ISAR Lean library with env=dev...")
    # Invoke lake -Kenv=dev build
    result = subprocess.run(["lake", "-R", "-Kenv=dev", "build"])
    sys.exit(result.returncode)

if __name__ == "__main__":
    main()
