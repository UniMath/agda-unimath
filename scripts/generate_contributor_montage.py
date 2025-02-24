import requests
from PIL import Image, ImageDraw
from io import BytesIO
import os

REPO_OWNER = "unimath"
REPO_NAME = "agda-unimath"
MAX_AVATARS_PER_ROW = 15

# Fetch contributors from GitHub API
response = requests.get(f"https://api.github.com/repos/{REPO_OWNER}/{REPO_NAME}/contributors")
contributors = response.json()

# Create a temporary directory for avatars
os.makedirs("avatars", exist_ok=True)

# Download profile pictures for each contributor
images = []
for contributor in contributors:
    login = contributor["login"]
    avatar_url = contributor["avatar_url"]
    avatar_response = requests.get(avatar_url)

    # Debugging information
    print(f"Fetching avatar for {login}: {avatar_url}")
    # print(f"Status code: {avatar_response.status_code}")

    if avatar_response.status_code == 200:
        try:
            img = Image.open(BytesIO(avatar_response.content)).convert("RGBA")
            # Create a round avatar
            size = (128, 128)
            mask = Image.new('L', size, 0)
            draw = ImageDraw.Draw(mask)
            draw.ellipse((0, 0) + size, fill=255)
            img = img.resize(size)
            img.putalpha(mask)
            images.append(img)
            img.save(f"avatars/{login}.png")
        except Exception as e:
            print(f"Warning: Could not process image for {login}: {e}")
    else:
        print(f"Warning: Failed to fetch avatar for {login}")

# Debugging information
print(f"Total contributor avatars: {len(images)}")

# Create a montage of all avatars
if images:
    avatar_width, avatar_height = images[0].size
    avatars_per_row = MAX_AVATARS_PER_ROW
    rows = (len(images) + avatars_per_row - 1) // avatars_per_row
    total_width = avatars_per_row * avatar_width
    total_height = rows * avatar_height

    montage = Image.new('RGBA', (total_width, total_height))

    x_offset = 0
    y_offset = 0
    for i, img in enumerate(images):
        montage.paste(img, (x_offset, y_offset), img)
        x_offset += img.width
        if (i + 1) % avatars_per_row == 0:
            x_offset = 0
            y_offset += img.height

    montage.save("website/images/contributor_montage.png")

# Clean up
for contributor in contributors:
    try:
        os.remove(f"avatars/{contributor['login']}.png")
    except FileNotFoundError:
        pass
os.rmdir("avatars")
