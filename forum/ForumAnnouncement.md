# Welcome to the MGWiki Forum

This is a forum for discussing Megalodon/Proofgold/MGWiki topics by editing and pushing Markdown files to the forum/ directory. Below is an example discussion and simple instructions on how to participate.

## Example Discussion

### **Topic: Improving the Documentation**

**User1** (2024-12-11, 12:00 PM UTC):
What are some ways we can create more docs?

> **User2** (2024-12-11, 12:30 PM UTC):
> I suggest XYZ.
>
> > **User3** (2024-12-11, 1:00 PM UTC):
> > Great idea! We could also include ABC.

---

## How to Post

1. **Pull the Latest Changes:**
   ```bash
   git pull
   ```

2. **Create or Edit a Discussion:**
   - To start a new discussion, create a new `.md` file in the `forum/` directory with a descriptive name (e.g., `docs-improvements.md`).
   - To reply, open the appropriate `.md` file and add your comment below the relevant section using the format shown in the example.

3. **Sign Your Comment:**
   - Include your username and the current timestamp (e.g., `**UserName** (YYYY-MM-DD, HH:MM UTC)`).
   - Example:
     ```markdown
     > **YourName** (2024-12-11, 2:00 PM UTC):
     > I agree with this suggestion and propose we add more details.
     ```

4. **Commit Your Changes:**
   ```bash
   git add forum/<file-name>.md
   git commit -m "Added reply to <topic>"
   git push
   ```

That's it! Your message will now be visible to everyone when they pull the latest changes.

If you also want to generate .html locally, run:
   ```bash
   pandoc foo.md -o foo.html
   ```



Happy discussing!
