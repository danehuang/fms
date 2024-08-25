import os


if __name__ == "__main__":
    files = [os.path.join("_includes", name) for name in os.listdir("_includes") if os.path.isfile(os.path.join("_includes", name)) and name.endswith("html")]
    for file in files:
        print("Patching", file)

        # Read the file and store lines
        with open(file, 'r') as f:
            lines = f.readlines()

        # Process lines and replace based on condition
        with open(file, 'w') as f:
            for line in lines:
                if '<link href="coqdoc.css" rel="stylesheet" type="text/css" />'  in line:
                    f.write(line.replace('<link href="coqdoc.css" rel="stylesheet" type="text/css" />', """<link rel="stylesheet" href="{{ 'assets/coqdoc.css' | relative_url }}">"""))
                elif '<!DOCTYPE html PUBLIC "-//W3C//DTD XHTML 1.0 Strict//EN"' in line:
                    # print("HERE1")
                    continue
                elif '"http://www.w3.org/TR/xhtml1/DTD/xhtml1-strict.dtd">' in line:
                    continue
                elif '<h1 class="libtitle">' in line:
                    continue
                else:
                    f.write(line)
    