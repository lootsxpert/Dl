FROM python:3.11-slim

ENV PYTHONUNBUFFERED=1 \
    PYTHONDONTWRITEBYTECODE=1 \
    PIP_NO_CACHE_DIR=1 \
    PIP_DISABLE_PIP_VERSION_CHECK=1

WORKDIR /app

# build-essential is only needed if pip has to compile TgCrypto from source
# (no matching wheel); it is removed in the same layer to keep the image small.
COPY requirements.txt .
RUN apt-get update \
    && apt-get install -y --no-install-recommends build-essential ca-certificates \
    && pip install --no-cache-dir -r requirements.txt \
    && apt-get purge -y --auto-remove build-essential \
    && rm -rf /var/lib/apt/lists/*

COPY bot.py .

# Pyrogram writes <session>.session and the bot writes downloads/ at runtime,
# so the app directory must be writable by the non-root user.
RUN useradd --create-home --uid 10001 appuser \
    && mkdir -p /app/downloads \
    && chown -R appuser:appuser /app
USER appuser

# Render overrides this with its own $PORT; the default keeps local runs working.
ENV PORT=8080
EXPOSE 8080

CMD ["python", "bot.py"]
