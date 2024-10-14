import sys, os

if __name__ == "__main__":
    folder = sys.argv[1]
    if not os.path.exists(folder):
        print("Folder does not exist")
        sys.exit()
    # Recursively get the absolute path for each file
    files = []
    for root, _, file in os.walk(folder):
        for f in file:
            # Add absolute path to the list
            files.append(os.path.abspath(os.path.join(root, f)))
    files.sort()
    with open(os.path.join(folder, "list.txt"), "w") as f:
        for file in files:
            f.write(file + "\n")
    print("Done")